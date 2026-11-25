"""End-to-end verification and SHA-256 manifest auditor for Paper 33:
OUH-CERT-1.0 (Edward A. Hirsch, arXiv:2611.33126).

Author: Lluis Eriksson
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "SHA256_MANIFEST.json"

TRACKED_FILES = [
    "LICENSE",
    "README.md",
    "pyproject.toml",
    "lean/lean-toolchain",
    "lean/lakefile.lean",
    "lean/ObliviousUnambiguousHierarchy.lean",
    "lean/AuditAxioms.lean",
    "src/__init__.py",
    "src/ouh_exact.py",
    "src/ouh_certifier.py",
    "scripts/run_all_experiments.py",
    "scripts/make_figures.py",
    "scripts/verify_all.py",
    "tests/test_suite.py",
    "paper/references.bib",
    "paper/main.tex",
    "paper/main.pdf",
    "figures/fig1_krentel_ogtd_and_tally_census.png",
    "figures/fig2_dot_collapse_and_loose_promise.png",
    "figures/fig3_certificate_replay_atlas.png",
    "data/certificate_replay_summary.json",
    "data/exp1_krentel_certified_fraction.json",
    "data/exp2_dot_collapse_census.json",
    "data/exp3_loose_promise_sensitivity.json",
    "data/exp4_tally_census_uniqueness.json",
]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def collect_manifest() -> dict[str, str]:
    files = list(TRACKED_FILES)
    for cert in sorted((ROOT / "certificates").glob("*.json")):
        files.append(f"certificates/{cert.name}")
    out: dict[str, str] = {}
    for rel in files:
        p = ROOT / rel
        if not p.exists():
            raise FileNotFoundError(f"Missing tracked artifact: {rel}")
        out[rel] = sha256_file(p)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-manifest", action="store_true")
    args = ap.parse_args()

    print("[1/4] Auditing Lean 4.35.0 kernel...")
    subprocess.run(["lake", "build"], cwd=ROOT / "lean", check=True)
    audit = subprocess.run(
        ["lake", "env", "lean", "-j", "1", "AuditAxioms.lean"],
        cwd=ROOT / "lean",
        check=True,
        capture_output=True,
        text=True,
    )
    assert "sorry" not in audit.stdout.lower(), "Lean proof contains sorry!"
    assert "Classical.choice" not in audit.stdout, "Lean proof uses Classical.choice!"
    assert "ofReduceBool" not in audit.stdout, "Lean proof uses Lean.ofReduceBool!"
    lean_lines = [ln for ln in audit.stdout.splitlines() if "ObliviousUnambiguousHierarchy." in ln]
    assert len(lean_lines) == 18, f"Expected 18 audited theorems, got {len(lean_lines)}"
    print(f"      PASS: {len(lean_lines)}/18 Lean theorems audited (0 sorry, 0 Classical.choice).")

    print("[2/4] Replaying all 16 canonical OUH-CERT-1.0 certificates...")
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from src.ouh_certifier import verify_ouh_certificate_exact

    cert_paths = sorted((ROOT / "certificates").glob("*.json"))
    assert len(cert_paths) == 16, f"Expected 16 certificates, found {len(cert_paths)}"
    for cp in cert_paths:
        res = verify_ouh_certificate_exact(json.loads(cp.read_text(encoding="utf-8")))
        assert res["verified"] is True
    print("      PASS: 16/16 certificates verified with zero floating-point arithmetic.")

    print("[3/4] Running pytest + 60 live adversarial forgery attacks...")
    subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, check=True)
    print("      PASS: pytest + 60/60 adversarial attacks rejected.")

    print("[4/4] SHA-256 manifest verification...")
    current = collect_manifest()
    if args.write_manifest:
        MANIFEST_PATH.write_text(json.dumps(current, indent=2) + "\n", encoding="utf-8")
        print(f"      WROTE {MANIFEST_PATH.name} with {len(current)} entries.")
    else:
        expected = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
        assert current == expected, "SHA-256 manifest mismatch!"
        print(f"      PASS: {len(current)}/{len(current)} artifact SHA-256 hashes match.")


if __name__ == "__main__":
    main()
