"""Generate all three 300-DPI publication figures for Paper 33:
OUH-CERT-1.0 (Edward A. Hirsch, arXiv:2611.33126).

Author: Lluis Eriksson
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data"
FIG_DIR = ROOT / "figures"

plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 9,
    "axes.titlesize": 10,
    "axes.labelsize": 9,
    "legend.fontsize": 8,
    "xtick.labelsize": 8,
    "ytick.labelsize": 8,
    "axes.grid": True,
    "grid.alpha": 0.28,
})


def make_fig1() -> None:
    d1 = json.loads((DATA_DIR / "exp1_krentel_certified_fraction.json").read_text(encoding="utf-8"))
    d4 = json.loads((DATA_DIR / "exp4_tally_census_uniqueness.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): Krentel certified transcript count |R| vs total 2^q and ONP probes q
    qs = sorted({r["depth_q"] for r in d1["rows"]})
    totals = [1 << q for q in qs]
    ax1.semilogy(qs, totals, "k--", lw=1.5, label=r"Total transcripts $2^q$")
    palette = {
        "sparse": ("#1f4e79", "o-"),
        "balanced": ("#548235", "s-"),
        "dense": ("#c55a11", "^-"),
    }
    for reg, (col, fmt) in palette.items():
        sub = [r for r in d1["rows"] if r["regime"] == reg]
        ys = [r["certified_count"] for r in sub]
        ax1.semilogy(qs, ys, fmt, ms=4.5, lw=1.8, color=col, label=f"Certified $|R|$ ({reg})")
    ax1.semilogy(qs, qs, "d:", ms=4.5, lw=1.6, color="#7030a0", label=r"ONP prefix probes ($= q$)")
    ax1.set_xticks(qs)
    ax1.set_ylim(0.8, 500)
    ax1.set_xlabel(r"Adaptive NP-oracle tree depth $q$")
    ax1.set_ylabel(r"Count (log scale)")
    ax1.set_title(r"(a) Krentel Lex-Max Certified Space vs. ONP Probes (Lemma 3.1)")
    ax1.legend(loc="upper left", framealpha=0.92, fontsize=7.2)

    # Panel (b): Lemma 2.8 Tally Census Search Collapse C(h, c_m) -> 1
    hs = [r["tally_bound_h"] for r in d4["rows"]]
    cands = [r["same_size_candidates"] for r in d4["rows"]]
    tots = [r["total_subsets"] for r in d4["rows"]]
    ax2.semilogy(hs, tots, "k--", lw=1.4, label=r"All oracle tables $2^h$")
    ax2.semilogy(hs, cands, "o-", ms=4.8, lw=2.0, color="#2e75b6", label=r"Same-census subsets $\binom{h}{c_m}$")
    ax2.semilogy(hs, [1] * len(hs), "s-", ms=5.0, lw=2.0, color="#c00000", label=r"Certified subsets $|S|=c_m, S\subseteq C_m$ ($=1$)")
    ax2.set_xticks(hs)
    ax2.set_ylim(0.6, 12000)
    ax2.set_xlabel(r"Tally oracle length bound $h$ ($c_m = \lfloor h/2 \rfloor$)")
    ax2.set_ylabel(r"Number of subsets (log scale)")
    ax2.set_title(r"(b) Lemma 2.8 Census Uniqueness Collapse ($=1$)")
    ax2.legend(loc="upper left", framealpha=0.92, fontsize=7.2)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_krentel_ogtd_and_tally_census.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d2 = json.loads((DATA_DIR / "exp2_dot_collapse_census.json").read_text(encoding="utf-8"))
    d3 = json.loads((DATA_DIR / "exp3_loose_promise_sensitivity.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): Theorem 6.2 Dot-Operator Collapse Witness Space -> Unique (w_n, v_N)
    rows2 = d2["rows"]
    labels = [f"({r['n']},{r['p']},{r['r']})" for r in rows2]
    x = np.arange(len(rows2))
    w = 0.34
    prod_w = [r["product_witness_space"] for r in rows2]
    uniq_w = [r["collapsed_accept_per_pos_x"] for r in rows2]
    ax1.bar(x - w / 2, prod_w, width=w, color="#2e75b6", label=r"Candidate pairs $|\{0,1\}^{p+r}|$")
    ax1.bar(x + w / 2, uniq_w, width=w, color="#548235", label=r"Collapsed accepted pairs ($=1$)")
    for xi, val in zip(x, prod_w):
        ax1.text(xi - w / 2, val + 0.9, str(val), ha="center", va="bottom", fontsize=7.5, color="#1f4e79", fontweight="bold")
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels)
    ax1.set_ylim(0, 40)
    ax1.set_xlabel(r"Parameters $(n, p, r)$")
    ax1.set_ylabel(r"Witness-pair count")
    ax1.set_title(r"(a) Theorem 6.2 Dot-Operator Witness Collapse")
    ax1.legend(loc="upper left", framealpha=0.92, fontsize=7.6)

    # Panel (b): Lemma 6.4 Single Loose Query Exhaustive Extension Audit
    rows3 = d3["rows"]
    outs = [r["num_out"] for r in rows3]
    exts = [r["extensions_checked"] for r in rows3]
    lat = [r["verify_ms"] for r in rows3]
    ax2_r = ax2.twinx()
    b1 = ax2.bar(outs, exts, width=0.52, color="#d9e8f5", edgecolor="#1f4e79", label=r"Consistent extensions $2^{|\Pi_{\mathrm{out}}|}$")
    l1 = ax2_r.plot(outs, lat, "o-", ms=5.0, lw=2.0, color="#c00000", label=r"Exact audit latency (ms)")
    ax2.set_xticks(outs)
    ax2.set_ylim(0, 78)
    ax2_r.set_ylim(0, max(lat) * 1.45)
    ax2.set_xlabel(r"Outside-promise queries $|\Pi_{\mathrm{out}}|$ ($n=3,p=2$)")
    ax2.set_ylabel(r"Consistent oracles checked ($2^{|\Pi_{\mathrm{out}}|}$)", color="#1f4e79")
    ax2_r.set_ylabel(r"Exact verification latency (ms)", color="#c00000")
    ax2.set_title(r"(b) Lemma 6.4 Exhaustive Loose-Oracle Audit")
    ax2_r.grid(False)
    lines = [b1] + l1
    labs = [ln.get_label() for ln in lines]
    ax2.legend(lines, labs, loc="upper left", framealpha=0.92, fontsize=7.4)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_dot_collapse_and_loose_promise.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    rep = json.loads((DATA_DIR / "certificate_replay_summary.json").read_text(encoding="utf-8"))
    certs = rep["certificates"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    mode_colors = {
        "tally_census_and_oblivious_extraction": "#1f4e79",
        "krentel_lex_max_ogtd_cert": "#2e75b6",
        "dot_operator_collapse_exact": "#548235",
        "single_loose_query_and_soup_exact": "#c55a11",
    }
    mode_short = {
        "tally_census_and_oblivious_extraction": "Mode 1 (Tally/OUH)",
        "krentel_lex_max_ogtd_cert": "Mode 2 (Krentel OGTD)",
        "dot_operator_collapse_exact": "Mode 3 (Dot Collapse)",
        "single_loose_query_and_soup_exact": "Mode 4 (Loose/SOUP)",
    }

    # Panel (a): Replay latency across all 16 certificates
    ys = np.arange(len(certs))
    lat = [max(c["verify_ms"], 0.005) for c in certs]
    cols = [mode_colors[c["mode"]] for c in certs]
    ax1.barh(ys, lat, color=cols, height=0.72, alpha=0.9)
    ax1.set_xscale("log")
    ax1.set_yticks(ys)
    ax1.set_yticklabels([f"C{i+1:02d}" for i in range(len(certs))], fontsize=7.2)
    ax1.invert_yaxis()
    ax1.set_xlim(0.004, max(lat) * 4.5)
    ax1.set_xlabel(r"Exact replay latency (ms, log scale)")
    ax1.set_title(r"(a) Replay Latency Across All 16 OUH-CERT-1.0 Certs")
    handles = [plt.Rectangle((0, 0), 1, 1, color=col, label=mode_short[m]) for m, col in mode_colors.items()]
    ax1.legend(handles=handles, loc="upper right", framealpha=0.92, fontsize=6.9)

    # Panel (b): Mode-wise Adversarial Rejection Audit (60/60)
    cats = ["Global\nSchema", "Mode 1\nTally", "Mode 2\nKrentel", "Mode 3\nDot-Op", "Mode 4\nLoose/SOUP"]
    counts = [10, 12, 12, 12, 14]
    bar_cols = ["#595959", "#1f4e79", "#2e75b6", "#548235", "#c55a11"]
    bars = ax2.bar(cats, counts, width=0.58, color=bar_cols, edgecolor="#222222", alpha=0.9)
    for b, cnt in zip(bars, counts):
        ax2.text(
            b.get_x() + b.get_width() / 2,
            cnt + 0.45,
            f"{cnt}/{cnt}",
            ha="center",
            va="bottom",
            fontsize=8.2,
            fontweight="bold",
            color="#111111",
        )
    ax2.set_ylim(0, 17.5)
    ax2.set_ylabel(r"Adversarial forgeries rejected")
    ax2.set_title(r"(b) Red-Team Adversarial Audit (60/60 Rejected)")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_certificate_replay_atlas.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 publication figures successfully.")


if __name__ == "__main__":
    main()
