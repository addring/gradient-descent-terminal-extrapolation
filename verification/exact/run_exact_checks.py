"""Run the finite exact audit with the Python standard library only."""
from pathlib import Path
from fractions import Fraction as F
import json
import subprocess
import sys

from check_asymptotic import exact_checks

ROOT = Path(__file__).resolve().parent

def run_child(name):
    result = subprocess.run(
        [sys.executable, str(ROOT / name)],
        cwd=ROOT, capture_output=True, text=True,
    )
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise RuntimeError(name + " failed")

def main():
    # Explicit regression examples showing the two original formulas fail.
    e = F(7, 3)
    q = F(5, 3)
    assert e != q - 1 and 1/e - 1/q < 0
    assert e == q - 1 + F(10, 6)
    assert F(29, 11) > F(11, 5)
    assert F(29, 11) <= F(33, 10)

    energy_counts = exact_checks()
    run_child("check_certificates.py")
    run_child("check_counterexamples.py")
    certificate = json.loads((ROOT / "verification.json").read_text())
    counterexamples = json.loads((ROOT / "results.json").read_text())
    summary = {
        "passed": True,
        "scope": "Finite exact checks; general statements are proved in proof.md.",
        "old_formula_failure_regressions": 2,
        "energy_exact_counts": energy_counts,
        "certificate_identity_cases": certificate["certificate_identity_cases"],
        "complete_kkt_and_flow_cases": len(certificate["flow_cases"]),
        "psd_identity_vectors": certificate["exact_psd_identity_total"],
        "counterexample_cases": len(counterexamples),
        "counterexample_ordered_constraints": sum(x["ordered_constraints"] for x in counterexamples),
        "counterexample_strict_constraints": sum(x["strict_constraints"] for x in counterexamples),
        "counterexample_zero_constraints": sum(x["zero_constraints"] for x in counterexamples),
        "arithmetic": "fractions.Fraction, with no floating point tolerance for pass/fail",
    }
    (ROOT / "exact_summary.json").write_text(
        json.dumps(summary, ensure_ascii=False, indent=2) + "\n"
    )
    print(json.dumps(summary, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()
