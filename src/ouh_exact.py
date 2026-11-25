"""Pure-stdlib exact combinatorial & oracle-simulation engine for Paper 33:
A Note on Input-Oblivious Unambiguous Hierarchies
(Edward A. Hirsch, arXiv:2611.33126, Nov 24, 2026).

ZERO floating-point arithmetic anywhere.
Author: Lluis Eriksson
"""
from __future__ import annotations

import itertools
from typing import Dict, List, Sequence, Set, Tuple


def cantor_pair(a: int, b: int) -> int:
    """Exact Cantor pairing pi(a, b) = (a+b)*(a+b+1)//2 + b."""
    if a < 0 or b < 0:
        raise ValueError("Cantor pairing requires non-negative integers")
    s = a + b
    return (s * (s + 1)) // 2 + b


def bitstrings(length: int) -> List[str]:
    """All binary strings of exact length `length` in lexicographical order."""
    return ["".join(bits) for bits in itertools.product("01", repeat=length)]


def check_oblivious_unambiguous(
    n: int, p: int, acc_table: Dict[str, List[str]]
) -> Tuple[bool, str | None, Set[str]]:
    """Verify whether a finite verifier V : {0,1}^n x {0,1}^p -> {0,1} (given as
    mapping x -> list of accepted witnesses w) is strictly OUP (input-oblivious unambiguous).
    Returns (is_oup, shared_witness_or_none_if_empty, accepted_language_L)."""
    xs = bitstrings(n)
    lang: Set[str] = set()
    shared_w: str | None = None
    for x in xs:
        ws = acc_table.get(x, [])
        if len(ws) > 1:
            return False, None, set()
        if len(ws) == 1:
            w = ws[0]
            if len(w) != p or any(ch not in "01" for ch in w):
                return False, None, set()
            if shared_w is None:
                shared_w = w
            elif w != shared_w:
                return False, None, set()
            lang.add(x)
    return True, shared_w, lang


def extract_oblivious_witness_via_tally_bits(
    n: int, p: int, acc_table: Dict[str, List[str]]
) -> str:
    """Theorem 4.1: Reconstruct w_n bit-by-bit via p parallel tally bit queries
    W_i = 1 iff exists (x, w) with V(x, w) = 1 and w[i] == '1' (gives 0^p if L = empty)."""
    out_bits: List[str] = []
    for i in range(p):
        found = any(
            w[i] == "1"
            for ws in acc_table.values()
            for w in ws
        )
        out_bits.append("1" if found else "0")
    return "".join(out_bits)


def simulate_adaptive_tree_and_krentel(
    depth_q: int,
    query_map: Dict[str, str],
    oracle_yes_queries: Set[str],
) -> Tuple[str, List[str], List[str]]:
    """Lemma 3.1: Given an adaptive oracle query tree mapping each prefix (length < q)
    to its query string, and the set of YES queries of the NP oracle A:
    Returns (true_transcript a*, all_certified_transcripts R, prefix_search_trace)."""
    # 1. Compute true transcript a*
    pref = ""
    for _ in range(depth_q):
        q_str = query_map[pref]
        ans = "1" if q_str in oracle_yes_queries else "0"
        pref += ans
    true_a = pref

    # 2. Enumerate ALL 2^q transcripts and check R(a): every '1' bit queries a YES query!
    certified: List[str] = []
    for cand in bitstrings(depth_q):
        ok = True
        p_cur = ""
        for j in range(depth_q):
            q_str = query_map[p_cur]
            bit = cand[j]
            if bit == "1" and q_str not in oracle_yes_queries:
                ok = False
                break
            p_cur += bit
        if ok:
            certified.append(cand)

    # 3. Replay Lemma 3.1 ONP binary prefix search: Q(c) = exists a >=_lex c in R
    recovered = ""
    trace: List[str] = []
    for j in range(depth_q):
        probe = recovered + "1" + ("0" * (depth_q - j - 1))
        ans = any(a >= probe for a in certified)
        recovered += "1" if ans else "0"
        trace.append(probe)

    assert recovered == true_a
    return true_a, certified, trace


def check_dot_operator_collapse_exact(
    n: int,
    p: int,
    r: int,
    inner_acc: Dict[str, List[str]],
) -> Tuple[bool, str | None, str | None, Set[str]]:
    """Theorem 6.2: Given inner OUP verifier V for bar{R} on keys 'x|w' (|x|=n, |w|=p, witness len r),
    verifies bar{R} in OUP (unique oblivious v_N), R defines an exists^{ou}.R language L (unique w_n),
    fixed-pair test V((0^n,0^p), v) OR V((0^n,1^p), v) pins down SOLELY v_N,
    and collapsed V'(x, (w,v)) accepts SOLELY (w_n, v_N) for x in L and none for x not in L."""
    if p < 1 or r < 1:
        return False, None, None, set()
    xs = bitstrings(n)
    ws = bitstrings(p)
    vs = bitstrings(r)

    # 1. Check bar{R} is strictly OUP with unique v_N
    v_N: str | None = None
    bar_R: Set[Tuple[str, str]] = set()
    for x in xs:
        for w in ws:
            key = f"{x}|{w}"
            acc_v = inner_acc.get(key, [])
            if len(acc_v) > 1:
                return False, None, None, set()
            if len(acc_v) == 1:
                v = acc_v[0]
                if len(v) != r or any(ch not in "01" for ch in v):
                    return False, None, None, set()
                if v_N is None:
                    v_N = v
                elif v != v_N:
                    return False, None, None, set()
                bar_R.add((x, w))
    if v_N is None:
        return False, None, None, set()

    # 2. Check R = complement of bar_R satisfies exists^{ou} condition (unique oblivious w_n)
    w_n: str | None = None
    lang_L: Set[str] = set()
    for x in xs:
        good_ws = [w for w in ws if (x, w) not in bar_R]
        if len(good_ws) > 1:
            return False, None, None, set()
        if len(good_ws) == 1:
            if w_n is None:
                w_n = good_ws[0]
            elif good_ws[0] != w_n:
                return False, None, None, set()
            lang_L.add(x)

    # 3. Fixed-pair refutation test on (0^n, 0^p) and (0^n, 1^p)
    x0, w0, w1 = "0" * n, "0" * p, "1" * p
    k0, k1 = f"{x0}|{w0}", f"{x0}|{w1}"
    pinned_vs = [v for v in vs if (v in inner_acc.get(k0, [])) or (v in inner_acc.get(k1, []))]
    if pinned_vs != [v_N]:
        return False, None, None, set()

    # 4. Verify collapsed verifier V'(x, (w,v)) = pin(v) AND NOT V((x,w), v)
    for x in xs:
        accepted_pairs: List[Tuple[str, str]] = []
        for w in ws:
            key = f"{x}|{w}"
            acc_v_set = set(inner_acc.get(key, []))
            for v in pinned_vs:
                if v not in acc_v_set:
                    accepted_pairs.append((w, v))
        if x in lang_L:
            if accepted_pairs != [(w_n, v_N)]:
                return False, None, None, set()
        else:
            if accepted_pairs:
                return False, None, None, set()

    return True, w_n, v_N, lang_L


def check_single_loose_query_and_soup(
    n: int,
    p: int,
    pi_yes: Set[str],
    pi_no: Set[str],
    pi_out: Set[str],
    query_of: Dict[str, str],
    v0_acc: Set[str],
    v1_acc: Set[str],
) -> Tuple[bool, Set[str], Set[str], str | None]:
    """Lemma 6.4 & Theorem 6.5: Exhaustively checks ALL 2^{|pi_out|} language extensions O
    consistent with promise (pi_yes, pi_no), verifies loose OUP consistency (identical language L
    and identical unique oblivious witness w_n across every O), computes sensitive set T,
    and confirms every (x,w) in T queries inside pi_yes U pi_no."""
    if (pi_yes & pi_no) or (pi_yes & pi_out) or (pi_no & pi_out):
        return False, set(), set(), None
    promise_set = pi_yes | pi_no
    all_queries = promise_set | pi_out
    xs = bitstrings(n)
    ws = bitstrings(p)
    out_list = sorted(pi_out)

    ref_lang: Set[str] | None = None
    ref_witness: str | None = None

    for bits in itertools.product((0, 1), repeat=len(out_list)):
        oracle_O = set(pi_yes) | {q for q, b in zip(out_list, bits) if b == 1}
        acc_table: Dict[str, List[str]] = {x: [] for x in xs}
        for x in xs:
            for w in ws:
                key = f"{x}|{w}"
                q = query_of[key]
                if q not in all_queries:
                    return False, set(), set(), None
                ans = 1 if q in oracle_O else 0
                if (key in v1_acc) if ans == 1 else (key in v0_acc):
                    acc_table[x].append(w)
        ok, w_n, lang = check_oblivious_unambiguous(n, p, acc_table)
        if not ok:
            return False, set(), set(), None
        if ref_lang is None:
            ref_lang = lang
            ref_witness = w_n
        else:
            if lang != ref_lang or w_n != ref_witness:
                return False, set(), set(), None

    sensitive_T: Set[str] = set()
    for x in xs:
        for w in ws:
            key = f"{x}|{w}"
            if (key in v0_acc) != (key in v1_acc):
                sensitive_T.add(key)
                if query_of[key] not in promise_set:
                    return False, set(), set(), None

    return True, sensitive_T, ref_lang or set(), ref_witness
