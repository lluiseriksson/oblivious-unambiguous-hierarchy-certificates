"""Comprehensive pytest suite + 60 live adversarial forgery attacks for Paper 33:
OUH-CERT-1.0 (Edward A. Hirsch, arXiv:2611.33126).

Author: Lluis Eriksson
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

import pytest

from src.ouh_certifier import OUHCertificateError, verify_ouh_certificate_exact
from src.ouh_exact import cantor_pair, simulate_adaptive_tree_and_krentel

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load_cert(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{name}.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_pass() -> None:
    cert_files = sorted(CERT_DIR.glob("*.json"))
    assert len(cert_files) == 16
    for path in cert_files:
        cert = json.loads(path.read_text(encoding="utf-8"))
        res = verify_ouh_certificate_exact(cert)
        assert res["verified"] is True


def test_exact_mathematical_invariants() -> None:
    # 1. Cantor pairing injectivity on [0..15] x [0..15]
    seen = set()
    for a in range(16):
        for b in range(16):
            val = cantor_pair(a, b)
            assert val not in seen
            seen.add(val)

    # 2. Krentel lex-max invariant on exhaustive depth-4 adaptive tree
    qmap = {pref: f"q_{k}_{pref}" for k in range(4) for pref in ["".join(b) for b in __import__("itertools").product("01", repeat=k)]}
    yes_set = {v for i, v in enumerate(sorted(qmap.values())) if i % 2 == 0}
    true_a, certified, trace = simulate_adaptive_tree_and_krentel(4, qmap, yes_set)
    assert max(certified) == true_a
    assert len(trace) == 4


def test_adversarial_red_team_forgeries() -> None:
    m1 = _load_cert("mode1_tally_n2_p3_nonempty")
    m2 = _load_cert("mode2_krentel_q3_sparse")
    m3 = _load_cert("mode3_dot_collapse_n2_p1_r2")
    m4 = _load_cert("mode4_loose_soup_n2_p1_out2")

    def mut(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
        c = copy.deepcopy(base)
        fn(c)
        return c

    attacks: List[Tuple[str, Any]] = [
        # --- Global / Schema / Type Confusion (10) ---
        ("root_not_dict", [1, 2, 3]),
        ("wrong_schema", mut(m1, lambda c: c.__setitem__("schema", "OUH-CERT-0.9"))),
        ("unknown_mode", mut(m1, lambda c: c.__setitem__("mode", "fake_mode"))),
        ("empty_name", mut(m1, lambda c: c.__setitem__("name", "  "))),
        ("float_injected", mut(m1, lambda c: c.__setitem__("claimed_census_cm", 4.0))),
        ("bool_for_int", mut(m1, lambda c: c.__setitem__("input_len_n", True))),
        ("extra_key_m1", mut(m1, lambda c: c.__setitem__("extra", 1))),
        ("missing_key_m1", mut(m1, lambda c: c.pop("claimed_lang_size"))),
        ("non_bit_char", mut(m1, lambda c: c.__setitem__("claimed_extracted_witness", "102"))),
        ("wrong_bit_len", mut(m1, lambda c: c.__setitem__("claimed_extracted_witness", "10"))),

        # --- Mode 1: Tally Census & Oblivious Extraction Forgeries (12) ---
        ("m1_n_out_of_range", mut(m1, lambda c: c.__setitem__("input_len_n", 6))),
        ("m1_p_zero", mut(m1, lambda c: c.__setitem__("witness_len_p", 0))),
        ("m1_h_out_of_range", mut(m1, lambda c: c.__setitem__("tally_bound_h", 33))),
        ("m1_tally_val_oob", mut(m1, lambda c: c["tally_set_Cm"].append(9))),
        ("m1_tally_dup", mut(m1, lambda c: c["tally_set_Cm"].append(1))),
        ("m1_wrong_census", mut(m1, lambda c: c.__setitem__("claimed_census_cm", 3))),
        ("m1_missing_input_key", mut(m1, lambda c: c["acc_table"].pop("00"))),
        ("m1_ambiguous_two_witnesses", mut(m1, lambda c: c["acc_table"].__setitem__("01", ["101", "110"]))),
        ("m1_non_oblivious_diff_witness", mut(m1, lambda c: c["acc_table"].__setitem__("11", ["010"]))),
        ("m1_dup_witness_in_list", mut(m1, lambda c: c["acc_table"].__setitem__("01", ["101", "101"]))),
        ("m1_wrong_lang_size", mut(m1, lambda c: c.__setitem__("claimed_lang_size", 3))),
        ("m1_wrong_extracted_w", mut(m1, lambda c: c.__setitem__("claimed_extracted_witness", "000"))),

        # --- Mode 2: Krentel Lex-Max & OUGTD Forgeries (12) ---
        ("m2_q_too_small", mut(m2, lambda c: c.__setitem__("depth_q", 1))),
        ("m2_q_too_large", mut(m2, lambda c: c.__setitem__("depth_q", 9))),
        ("m2_missing_prefix", mut(m2, lambda c: c["query_map"].pop("0"))),
        ("m2_empty_query_str", mut(m2, lambda c: c["query_map"].__setitem__("", "  "))),
        ("m2_dup_yes_query", mut(m2, lambda c: c["oracle_yes_queries"].append(c["oracle_yes_queries"][0]))),
        ("m2_wrong_lex_max", mut(m2, lambda c: c.__setitem__("claimed_lex_max_transcript", "000"))),
        ("m2_wrong_cert_count", mut(m2, lambda c: c.__setitem__("claimed_certified_count", c["claimed_certified_count"] + 1))),
        ("m2_wrong_probe_len", mut(m2, lambda c: c["claimed_prefix_probes"].pop())),
        ("m2_tampered_probe", mut(m2, lambda c: c["claimed_prefix_probes"].__setitem__(0, "000"))),
        ("m2_wrong_tester_acc", mut(m2, lambda c: c.__setitem__("claimed_tester_unique_acc", "000"))),
        ("m2_extra_key", mut(m2, lambda c: c.__setitem__("extra", "x"))),
        ("m2_non_list_yes", mut(m2, lambda c: c.__setitem__("oracle_yes_queries", "q_0_root"))),

        # --- Mode 3: Dot-Operator Collapse Forgeries (12) ---
        ("m3_p_zero", mut(m3, lambda c: c.__setitem__("outer_witness_len_p", 0))),
        ("m3_r_zero", mut(m3, lambda c: c.__setitem__("inner_witness_len_r", 0))),
        ("m3_missing_pair_key", mut(m3, lambda c: c["inner_acc_table"].pop("00|0"))),
        ("m3_inner_ambiguous", mut(m3, lambda c: c["inner_acc_table"].__setitem__("00|0", ["10", "11"]))),
        ("m3_inner_non_oblivious", mut(m3, lambda c: c["inner_acc_table"].__setitem__("01|0", ["01"]))),
        ("m3_outer_ambiguous_both_in_R", mut(m3, lambda c: c["inner_acc_table"].__setitem__("00|0", []))),
        ("m3_outer_non_oblivious", mut(m3, lambda c: (c["inner_acc_table"].__setitem__("11|1", ["10"]), c["inner_acc_table"].__setitem__("11|0", [])))),
        ("m3_empty_lang_vacuous", mut(m3, lambda c: (c["inner_acc_table"].__setitem__("00|1", ["10"]), c["inner_acc_table"].__setitem__("11|1", ["10"])))),
        ("m3_wrong_outer_wn", mut(m3, lambda c: c.__setitem__("claimed_outer_wn", "0"))),
        ("m3_wrong_inner_vN", mut(m3, lambda c: c.__setitem__("claimed_inner_vN", "01"))),
        ("m3_wrong_lang_size", mut(m3, lambda c: c.__setitem__("claimed_lang_size", 3))),
        ("m3_dup_inner_witness", mut(m3, lambda c: c["inner_acc_table"].__setitem__("00|0", ["10", "10"]))),

        # --- Mode 4: Single Loose Query & SOUP Forgeries (14) ---
        ("m4_empty_pi_out_vacuous", mut(m4, lambda c: c.__setitem__("pi_out", []))),
        ("m4_overlapping_promise", mut(m4, lambda c: c["pi_no"].append(c["pi_yes"][0]))),
        ("m4_dup_pi_yes", mut(m4, lambda c: c["pi_yes"].append(c["pi_yes"][0]))),
        ("m4_sensitive_queries_outside_promise", mut(m4, lambda c: c["query_of"].__setitem__("00|1", "pout_0"))),
        ("m4_unknown_query_name", mut(m4, lambda c: c["query_of"].__setitem__("00|0", "unknown_q"))),
        ("m4_vacuous_empty_T", mut(m4, lambda c: c.__setitem__("v1_acc", []))),
        ("m4_wrong_sensitive_count", mut(m4, lambda c: c.__setitem__("claimed_sensitive_count", c["claimed_sensitive_count"] + 1))),
        ("m4_wrong_loose_lang_size", mut(m4, lambda c: c.__setitem__("claimed_loose_lang_size", 3))),
        ("m4_soup_Y_Z_overlap", mut(m4, lambda c: c["soup_Z_table"].__setitem__("00", ["0"]))),
        ("m4_soup_Y_Z_gap", mut(m4, lambda c: c["soup_Y_table"].__setitem__("00", []))),
        ("m4_soup_Y_ambiguous", mut(m4, lambda c: c["soup_Y_table"].__setitem__("00", ["0", "1"]))),
        ("m4_soup_Y_non_oblivious", mut(m4, lambda c: c["soup_Y_table"].__setitem__("10", ["0"]))),
        ("m4_wrong_soup_shared_w", mut(m4, lambda c: c.__setitem__("claimed_soup_shared_witness", "0|0"))),
        ("m4_v1_acc_invalid_pair", mut(m4, lambda c: c["v1_acc"].append("99|9"))),
    ]

    assert len(attacks) == 60
    rejected = 0
    for attack_name, payload in attacks:
        with pytest.raises(OUHCertificateError, match=".+"):
            verify_ouh_certificate_exact(payload)
        rejected += 1
    assert rejected == 60
