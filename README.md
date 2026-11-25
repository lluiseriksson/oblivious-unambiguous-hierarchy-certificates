# Machine-Checked Exact Combinatorial Certificates for Input-Oblivious Unambiguous Hierarchies, Krentel Lex-Max OGTD Collapse, and Single-Query Promise Elimination

**Author:** Lluis Eriksson (prepared with transparent AI assistance via Google Antigravity)
**Target Reference:** Edward A. Hirsch, *A note on input-oblivious unambiguous hierarchies*, `arXiv:2611.33126` (November 24, 2026).
**Licenses:** Manuscript (`paper/main.tex`, `paper/main.pdf`) under `CC-BY-4.0`; code, Lean 4 proofs, and exact certificates under `MIT`.

## Highlights
- **Zero-Dependency Lean 4 Kernel (`lean/ObliviousUnambiguousHierarchy.lean`, Lean 4.35.0):** 18 constructive theorems, `0` `sorry`, `0` warnings, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, **11 zero-axiom theorems** (`none`).
- **Pure-Stdlib Zero-Float Verifier (`OUH-CERT-1.0`, `src/ouh_certifier.py`):** Four exact combinatorial verification modes covering Lemma 2.8 / Theorem 4.1 tally census and bit-by-bit oblivious extraction, Lemma 3.1 / Theorem 5.1 Krentel lex-max transcripts and `OUGTD` unique testers, Theorem 6.2 / Corollary 6.3 dot-operator collapse, and Lemma 6.4 / Theorem 6.5 / Proposition 6.6 single loose promise queries and `SOUP = OUP ∩ co-OUP`.
- **Canonical Atlas & Adversarial Audit:** 16/16 canonical certificates replayed in `0.038–0.789 ms`, exact sweeps across adaptive depths `q=2..8`, tally bounds `h=4..12`, and up to `2^6 = 64` consistent promise extensions, and **60/60 live adversarial forgery attacks rejected**.

## Quick Reproduction
```bash
# 1. Build & audit Lean 4 kernel
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..

# 2. Regenerate all 16 certificates, 4 exact experiments, and 3 figures
python scripts/run_all_experiments.py
python scripts/make_figures.py

# 3. Run full end-to-end verification (Lean + 16 certs + 60/60 attacks + SHA-256 manifest)
python scripts/verify_all.py
```
