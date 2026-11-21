#!/usr/bin/env python3
"""
Clean-Room Master Verification Runner for branches/spectral-inertia.

Safe under ALL three R4 modes:
  python3 -B run_all.py
  python3 -O -B run_all.py
  python3 -B -W error run_all.py
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from spectral_inertia.examples.bloch_and_hessian_boxes import run_bloch_and_hessian_validations
from spectral_inertia.examples.fibral_truss_box import run_fibral_truss_validation
from spectral_inertia.examples.scan23848_benchmark import run_scan23848_benchmark
from tests.run_mutation_suite import run_all_mutants


def main() -> None:
    loader = unittest.TestLoader()
    suite = loader.discover(str(ROOT / "tests"), pattern="test_*.py")
    runner = unittest.TextTestRunner(verbosity=2, stream=sys.stderr)
    result = runner.run(suite)
    if not result.wasSuccessful():
        sys.exit(f"UNITTEST FAILED: failures={len(result.failures)}, errors={len(result.errors)}")

    mut_report = run_all_mutants()
    if mut_report["survivors"] != 0:
        sys.exit(f"MUTATION SUITE FAILED: {mut_report['survivors']} survivors")

    scan_report = run_scan23848_benchmark()
    truss_report = run_fibral_truss_validation()
    bloch_report = run_bloch_and_hessian_validations()

    summary = {
        "unittest": {
            "tests_run": result.testsRun,
            "failures": len(result.failures),
            "errors": len(result.errors),
            "ok": True,
        },
        "mutation_suite_r5": {
            "total_mutants": mut_report["total_mutants"],
            "killed": mut_report["killed"],
            "survivors": mut_report["survivors"],
            "kill_rate_pct": mut_report["kill_rate_pct"],
        },
        "track_a_scan23848_summary": {
            "mode_a_strict_ceil_wins_over_R_opt": scan_report["mode_a_strict_ceil_wins_over_R_opt"],
            "mode_b_all_exact_1": all(r["Hankel4_minus_1_is_exact_1"] for r in scan_report["mode_b_tau0_rows"]),
            "three_component_mode_b": scan_report["three_component_mode_b_benchmark"],
        },
        "track_b_validations": {
            "fibral_truss_full_status": truss_report["full_box_0p7_1p3_x_0p9_1p5"]["status"],
            "fibral_truss_taut_status": truss_report["taut_subbox_certified_PD"]["status"],
            "fibral_truss_buckled_status": truss_report["buckled_subbox_certified_PD"]["status"],
            "bloch_gapped_status": bloch_report["bloch_2d_gapped_complex_hermitian_box"]["status"],
            "bloch_dirac_status": bloch_report["bloch_2d_interior_dirac_singularity_box"]["status"],
            "morse_saddle_status": bloch_report["morse_3x3_constant_saddle_box"]["status"],
            "morse_bifurcation_status": bloch_report["morse_3x3_irrational_bifurcation_box"]["status"],
        },
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
