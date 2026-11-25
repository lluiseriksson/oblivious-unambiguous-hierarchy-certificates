"""Pure-stdlib zero-float verifier for OUH-CERT-1.0 certificates.
Supports four exact combinatorial verification modes aligned with Edward A. Hirsch
(arXiv:2611.33126, Nov 24, 2026) "A note on input-oblivious unambiguous hierarchies":
  1. tally_census_and_oblivious_extraction (Lemma 2.8 & Thm 4.1: OUH subseteq P^{TALLY cap NP} subseteq P_||^{ONP})
  2. krentel_lex_max_ogtd_cert             (Lemma 3.1 & Thm 5.1: OGTD[NP] = OUGTD[FP^{ONP}, co-ONP, P])
  3. dot_operator_collapse_exact           (Thm 6.2 & Cor 6.3: exists^{ou}.co-OUP = OUP U co-OUP)
  4. single_loose_query_and_soup_exact     (Lemma 6.4, Thm 6.5, Prop 6.6: OUP^{prOUP[1]} = OUP^{OUP[1]}, SOUP = OUP cap co-OUP)

Author: Lluis Eriksson
"""
from __future__ import annotations

from typing import Any, Dict, List, Set

from src.ouh_exact import (
    bitstrings,
    cantor_pair,
    check_dot_operator_collapse_exact,
    check_oblivious_unambiguous,
    check_single_loose_query_and_soup,
    extract_oblivious_witness_via_tally_bits,
    simulate_adaptive_tree_and_krentel,
)

SCHEMA_VERSION = "OUH-CERT-1.0"


class OUHCertificateError(ValueError):
    """Raised whenever any OUH-CERT-1.0 verification check fails."""


def _assert_strict_json_types(obj: Any, path: str = "root") -> None:
    t = type(obj)
    if t is int or t is str:
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise OUHCertificateError(f"Non-str dict key at {path}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    raise OUHCertificateError(f"Forbidden type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise OUHCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    return val


def _parse_bitstr(val: Any, length: int, name: str) -> str:
    if type(val) is not str or len(val) != length or any(c not in "01" for c in val):
        raise OUHCertificateError(f"{name} must be bitstring of length {length}, got {val!r}")
    return val


def _verify_mode1_tally_extraction(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "input_len_n", "witness_len_p",
        "tally_bound_h", "tally_set_Cm", "claimed_census_cm",
        "acc_table", "claimed_lang_size", "claimed_extracted_witness",
    }
    if set(cert.keys()) != req:
        raise OUHCertificateError(f"Mode 1 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["input_len_n"], "input_len_n")
    p = _parse_int(cert["witness_len_p"], "witness_len_p")
    h = _parse_int(cert["tally_bound_h"], "tally_bound_h")
    if not (1 <= n <= 5) or not (1 <= p <= 8) or not (1 <= h <= 32):
        raise OUHCertificateError("Require 1<=n<=5, 1<=p<=8, 1<=h<=32")

    cm_raw = cert["tally_set_Cm"]
    if type(cm_raw) is not list:
        raise OUHCertificateError("tally_set_Cm must be list")
    cm_set: Set[int] = set()
    for i, k in enumerate(cm_raw):
        kv = _parse_int(k, f"tally_set_Cm[{i}]")
        if not (1 <= kv <= h) or kv in cm_set:
            raise OUHCertificateError(f"tally_set_Cm[{i}] out of range 1..{h} or duplicate")
        cm_set.add(kv)
    if _parse_int(cert["claimed_census_cm"], "claimed_census_cm") != len(cm_set):
        raise OUHCertificateError(f"claimed_census_cm mismatch: exact={len(cm_set)}")

    # Verify Cantor pairing injectivity on all (n, i) for i=1..p
    pairs = {cantor_pair(n, i) for i in range(1, p + 1)}
    if len(pairs) != p:
        raise OUHCertificateError("Cantor pairing collision")

    acc_raw = cert["acc_table"]
    if type(acc_raw) is not dict:
        raise OUHCertificateError("acc_table must be dict")
    xs = set(bitstrings(n))
    if set(acc_raw.keys()) != xs:
        raise OUHCertificateError("acc_table keys must equal {0,1}^n")
    acc_table: Dict[str, List[str]] = {}
    for x, ws in acc_raw.items():
        if type(ws) is not list:
            raise OUHCertificateError(f"acc_table[{x}] must be list")
        cleaned = [_parse_bitstr(w, p, f"acc_table[{x}][{j}]") for j, w in enumerate(ws)]
        if len(set(cleaned)) != len(cleaned):
            raise OUHCertificateError(f"Duplicate witness in acc_table[{x}]")
        acc_table[x] = cleaned

    ok, shared_w, lang = check_oblivious_unambiguous(n, p, acc_table)
    if not ok:
        raise OUHCertificateError("Verifier violates OUP (not input-oblivious unambiguous)")
    extracted = extract_oblivious_witness_via_tally_bits(n, p, acc_table)
    expected_w = shared_w if shared_w is not None else ("0" * p)
    if extracted != expected_w:
        raise OUHCertificateError("Tally bit-by-bit extraction mismatch")
    if _parse_int(cert["claimed_lang_size"], "claimed_lang_size") != len(lang):
        raise OUHCertificateError(f"claimed_lang_size mismatch: exact={len(lang)}")
    if _parse_bitstr(cert["claimed_extracted_witness"], p, "claimed_extracted_witness") != extracted:
        raise OUHCertificateError(f"claimed_extracted_witness mismatch: exact={extracted!r}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n": n,
        "p": p,
        "census_cm": len(cm_set),
        "lang_size": len(lang),
        "extracted_witness": extracted,
    }


def _verify_mode2_krentel_ogtd(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "depth_q", "query_map", "oracle_yes_queries",
        "claimed_lex_max_transcript", "claimed_certified_count",
        "claimed_prefix_probes", "claimed_tester_unique_acc",
    }
    if set(cert.keys()) != req:
        raise OUHCertificateError(f"Mode 2 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    q = _parse_int(cert["depth_q"], "depth_q")
    if not (2 <= q <= 8):
        raise OUHCertificateError("Require 2 <= depth_q <= 8")

    qmap_raw = cert["query_map"]
    if type(qmap_raw) is not dict:
        raise OUHCertificateError("query_map must be dict")
    expected_prefixes = {p for k in range(q) for p in bitstrings(k)}
    if set(qmap_raw.keys()) != expected_prefixes:
        raise OUHCertificateError("query_map must specify query for every prefix of length < depth_q")
    qmap: Dict[str, str] = {}
    for pref, qstr in qmap_raw.items():
        if type(qstr) is not str or not qstr.strip():
            raise OUHCertificateError(f"Invalid query string at prefix {pref!r}")
        qmap[pref] = qstr

    yes_raw = cert["oracle_yes_queries"]
    if type(yes_raw) is not list or any(type(s) is not str or not s.strip() for s in yes_raw):
        raise OUHCertificateError("oracle_yes_queries must be list of non-empty strings")
    if len(set(yes_raw)) != len(yes_raw):
        raise OUHCertificateError("Duplicate entry in oracle_yes_queries")
    yes_set = set(yes_raw)

    true_a, certified, trace = simulate_adaptive_tree_and_krentel(q, qmap, yes_set)
    # Verify Krentel lex-max uniqueness and co-ONP tester Acc_T == {true_a}
    max_cert = max(certified)
    if max_cert != true_a:
        raise OUHCertificateError("Internal Krentel lex-max invariant failed")
    acc_T = [a for a in certified if not any(b > a for b in certified)]
    if acc_T != [true_a]:
        raise OUHCertificateError("co-ONP tester failed uniqueness")

    if _parse_bitstr(cert["claimed_lex_max_transcript"], q, "claimed_lex_max_transcript") != true_a:
        raise OUHCertificateError(f"claimed_lex_max_transcript mismatch: exact={true_a!r}")
    if _parse_int(cert["claimed_certified_count"], "claimed_certified_count") != len(certified):
        raise OUHCertificateError(f"claimed_certified_count mismatch: exact={len(certified)}")
    probes_raw = cert["claimed_prefix_probes"]
    if type(probes_raw) is not list or len(probes_raw) != q or probes_raw != trace:
        raise OUHCertificateError("claimed_prefix_probes mismatch with ONP prefix search")
    if _parse_bitstr(cert["claimed_tester_unique_acc"], q, "claimed_tester_unique_acc") != true_a:
        raise OUHCertificateError("claimed_tester_unique_acc mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "depth_q": q,
        "total_transcripts": 1 << q,
        "certified_count": len(certified),
        "lex_max": true_a,
    }


def _verify_mode3_dot_collapse(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "input_len_n", "outer_witness_len_p",
        "inner_witness_len_r", "inner_acc_table",
        "claimed_outer_wn", "claimed_inner_vN", "claimed_lang_size",
    }
    if set(cert.keys()) != req:
        raise OUHCertificateError(f"Mode 3 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["input_len_n"], "input_len_n")
    p = _parse_int(cert["outer_witness_len_p"], "outer_witness_len_p")
    r = _parse_int(cert["inner_witness_len_r"], "inner_witness_len_r")
    if not (1 <= n <= 4) or not (1 <= p <= 3) or not (1 <= r <= 3):
        raise OUHCertificateError("Require 1<=n<=4, 1<=p<=3, 1<=r<=3")

    inner_raw = cert["inner_acc_table"]
    if type(inner_raw) is not dict:
        raise OUHCertificateError("inner_acc_table must be dict")
    expected_keys = {f"{x}|{w}" for x in bitstrings(n) for w in bitstrings(p)}
    if set(inner_raw.keys()) != expected_keys:
        raise OUHCertificateError("inner_acc_table keys must cover all (x, w)")
    inner_acc: Dict[str, List[str]] = {}
    for k, vs in inner_raw.items():
        if type(vs) is not list:
            raise OUHCertificateError(f"inner_acc_table[{k}] must be list")
        cleaned = [_parse_bitstr(v, r, f"inner_acc_table[{k}][{j}]") for j, v in enumerate(vs)]
        if len(set(cleaned)) != len(cleaned):
            raise OUHCertificateError(f"Duplicate inner witness in {k}")
        inner_acc[k] = cleaned

    ok, w_n, v_N, lang_L = check_dot_operator_collapse_exact(n, p, r, inner_acc)
    if not ok or v_N is None:
        raise OUHCertificateError("Theorem 6.2 dot-operator collapse verification failed")
    if len(lang_L) == 0 or w_n is None:
        raise OUHCertificateError("Require non-empty language L for non-vacuous witness collapse")

    if _parse_bitstr(cert["claimed_outer_wn"], p, "claimed_outer_wn") != w_n:
        raise OUHCertificateError(f"claimed_outer_wn mismatch: exact={w_n!r}")
    if _parse_bitstr(cert["claimed_inner_vN"], r, "claimed_inner_vN") != v_N:
        raise OUHCertificateError(f"claimed_inner_vN mismatch: exact={v_N!r}")
    if _parse_int(cert["claimed_lang_size"], "claimed_lang_size") != len(lang_L):
        raise OUHCertificateError(f"claimed_lang_size mismatch: exact={len(lang_L)}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n": n,
        "p": p,
        "r": r,
        "collapsed_witness": f"{w_n}|{v_N}",
        "lang_size": len(lang_L),
    }


def _verify_mode4_loose_and_soup(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "input_len_n", "witness_len_p",
        "pi_yes", "pi_no", "pi_out", "query_of", "v0_acc", "v1_acc",
        "claimed_sensitive_count", "claimed_loose_lang_size",
        "soup_Y_table", "soup_Z_table", "claimed_soup_shared_witness",
    }
    if set(cert.keys()) != req:
        raise OUHCertificateError(f"Mode 4 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["input_len_n"], "input_len_n")
    p = _parse_int(cert["witness_len_p"], "witness_len_p")
    if not (1 <= n <= 4) or not (1 <= p <= 3):
        raise OUHCertificateError("Require 1<=n<=4, 1<=p<=3")

    def _str_set(key: str, max_len: int = 32) -> Set[str]:
        raw = cert[key]
        if type(raw) is not list or len(raw) > max_len or any(type(s) is not str or not s.strip() for s in raw):
            raise OUHCertificateError(f"{key} must be valid string list")
        if len(set(raw)) != len(raw):
            raise OUHCertificateError(f"{key} contains duplicates")
        return set(raw)

    pi_yes = _str_set("pi_yes")
    pi_no = _str_set("pi_no")
    pi_out = _str_set("pi_out", max_len=6)
    if len(pi_out) < 1:
        raise OUHCertificateError("Require at least 1 outside-promise query for non-vacuous Lemma 6.4 audit")

    expected_pairs = {f"{x}|{w}" for x in bitstrings(n) for w in bitstrings(p)}
    q_of_raw = cert["query_of"]
    if type(q_of_raw) is not dict or set(q_of_raw.keys()) != expected_pairs:
        raise OUHCertificateError("query_of must map every (x|w) pair to a query string")
    query_of: Dict[str, str] = {}
    for k, qv in q_of_raw.items():
        if type(qv) is not str or not qv.strip():
            raise OUHCertificateError(f"Invalid query in query_of[{k}]")
        query_of[k] = qv

    v0_acc = _str_set("v0_acc", max_len=128)
    v1_acc = _str_set("v1_acc", max_len=128)
    if not v0_acc.issubset(expected_pairs) or not v1_acc.issubset(expected_pairs):
        raise OUHCertificateError("v0_acc / v1_acc must be subsets of {0,1}^n x {0,1}^p")

    ok, sens_T, loose_lang, _ = check_single_loose_query_and_soup(
        n, p, pi_yes, pi_no, pi_out, query_of, v0_acc, v1_acc
    )
    if not ok:
        raise OUHCertificateError("Lemma 6.4 single-loose-query consistency / promise check failed")
    if len(sens_T) == 0:
        raise OUHCertificateError("Vacuous verifier with empty sensitive set T")
    if _parse_int(cert["claimed_sensitive_count"], "claimed_sensitive_count") != len(sens_T):
        raise OUHCertificateError(f"claimed_sensitive_count mismatch: exact={len(sens_T)}")
    if _parse_int(cert["claimed_loose_lang_size"], "claimed_loose_lang_size") != len(loose_lang):
        raise OUHCertificateError(f"claimed_loose_lang_size mismatch: exact={len(loose_lang)}")

    # Sub-check B: Proposition 6.6 SOUP = OUP cap co-OUP exact shared witness verification
    xs = set(bitstrings(n))
    def _parse_oup_table(field: str) -> Dict[str, List[str]]:
        raw = cert[field]
        if type(raw) is not dict or set(raw.keys()) != xs:
            raise OUHCertificateError(f"{field} must map every x in {{0,1}}^n")
        tbl: Dict[str, List[str]] = {}
        for x, ws in raw.items():
            if type(ws) is not list:
                raise OUHCertificateError(f"{field}[{x}] must be list")
            cleaned = [_parse_bitstr(w, p, f"{field}[{x}][{j}]") for j, w in enumerate(ws)]
            if len(set(cleaned)) != len(cleaned):
                raise OUHCertificateError(f"Duplicate witness in {field}[{x}]")
            tbl[x] = cleaned
        return tbl

    y_tbl = _parse_oup_table("soup_Y_table")
    z_tbl = _parse_oup_table("soup_Z_table")
    ok_y, w_y, lang_y = check_oblivious_unambiguous(n, p, y_tbl)
    ok_z, w_z, lang_z = check_oblivious_unambiguous(n, p, z_tbl)
    if not ok_y or not ok_z:
        raise OUHCertificateError("soup_Y_table or soup_Z_table violates OUP")
    if lang_y & lang_z or (lang_y | lang_z) != xs:
        raise OUHCertificateError("Y and Z do not decide complementary languages L and co-L")
    if lang_y != loose_lang:
        raise OUHCertificateError("SOUP language L does not match Lemma 6.4 loose-query language")

    x0 = "0" * n
    if x0 in lang_y:
        assert w_y is not None
        shared_soup_w = f"1|{w_y}"
    else:
        assert w_z is not None
        shared_soup_w = f"0|{w_z}"

    # Verify tagged witness uniqueness on 0^n across all (b, w) in {0,1} x {0,1}^p
    valid_tags = []
    for w in bitstrings(p):
        if w in y_tbl[x0]:
            valid_tags.append(f"1|{w}")
        if w in z_tbl[x0]:
            valid_tags.append(f"0|{w}")
    if valid_tags != [shared_soup_w]:
        raise OUHCertificateError("Proposition 6.6 shared tagged witness uniqueness failed")

    if cert["claimed_soup_shared_witness"] != shared_soup_w:
        raise OUHCertificateError(f"claimed_soup_shared_witness mismatch: exact={shared_soup_w!r}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "sensitive_count": len(sens_T),
        "loose_extensions_checked": 1 << len(pi_out),
        "soup_shared_witness": shared_soup_w,
    }


def verify_ouh_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    if type(cert) is not dict:
        raise OUHCertificateError("Certificate root must be a dict")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise OUHCertificateError(f"Invalid schema: {cert.get('schema')!r}")
    name = cert.get("name")
    if type(name) is not str or not name.strip():
        raise OUHCertificateError(f"Certificate name must be non-empty str, got {name!r}")
    mode = cert.get("mode")
    if mode == "tally_census_and_oblivious_extraction":
        return _verify_mode1_tally_extraction(cert)
    if mode == "krentel_lex_max_ogtd_cert":
        return _verify_mode2_krentel_ogtd(cert)
    if mode == "dot_operator_collapse_exact":
        return _verify_mode3_dot_collapse(cert)
    if mode == "single_loose_query_and_soup_exact":
        return _verify_mode4_loose_and_soup(cert)
    raise OUHCertificateError(f"Unknown mode: {mode!r}")
