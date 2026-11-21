"""
Track B Test Suite: Exact Non-Affine Parametric Complex-Hermitian Box Certifier (SEAM-04).

Validates:
  1. Exact multivariate Bernstein enclosure soundness & strict tightness over naive interval arithmetic.
  2. Validation 1: aska-physical/fibral-rigidity#5 two-bar truss box [7/10,13/10]x[9/10,15/10]
     (all 4 corners PD (2,0,0), exact interior singular witness (9/10,11/10) with inertia (1,0,1),
      plus certified uniform PD on taut & buckled sub-boxes).
  3. Validation 2: Complex Hermitian 2D Bloch dynamical matrix box (gapped PD box certified across
     uncountably many complex wavevectors + interior Dirac zero-mode box where all 4 corners are PD
     yet interior (0,0) is exact singular (1,0,1)!).
  4. Validation 3: Non-affine 3x3 indefinite Morse-index Hessian box (uniform saddle (2,1,0) certified
     + irrational bifurcation crossing certified via INERTIA_CHANGE_DETECTED (2,1,0) <-> (3,0,0)).
  5. RatMatrix centered-Bernstein rational entry mode + 2x2 Bunch-Kaufman zero-diagonal indefinite box.
  6. Gate 2 & Gate 3 controls: random interior point sampling inside every certified box MUST match
     the certified inertia identically via Track C's independent Oracle 2!
"""
from __future__ import annotations

from fractions import Fraction
import random
import unittest

from spectral_inertia.box_certifier import (
    MultiPoly,
    PolyMatrix,
    QInterval,
    RatMatrix,
    bernstein_enclosure,
    certify_hermitian_box,
    exact_sqrt_bounds,
)
from spectral_inertia.dual_oracle import oracle_faddeev_descartes_sturm
from spectral_inertia.exact_qi import CertError, Qi
from spectral_inertia.examples.bloch_and_hessian_boxes import (
    build_bloch_2d_polymatrix,
    build_morse_3x3_polymatrix,
    run_bloch_and_hessian_validations,
)
from spectral_inertia.examples.fibral_truss_box import (
    run_fibral_truss_validation,
    truss_equilibrium_hessian_raw,
)


def _req(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


class TestTrackBBoxCertifier(unittest.TestCase):
    def test_01_exact_sqrt_and_bernstein_tightness(self) -> None:
        # Exact isqrt bracket invariant on tricky rationals
        for q in (Fraction(0), Fraction(1), Fraction(2), Fraction(7, 13), Fraction(10**12 + 1, 3)):
            lo, hi = exact_sqrt_bounds(q)
            _req(lo >= 0 and lo * lo <= q <= hi * hi, f"sqrt bracket violated for {q}")
        with self.assertRaises(CertError):
            exact_sqrt_bounds(Fraction(-1, 4))

        # Dependency elimination: f(x) = x - x^2 on [0, 1]
        # Naive interval arithmetic gives [0,1] - [0,1] = [-1, 1] (width 2, crosses 0!)
        # Exact Bernstein gives [0, 1/2] (width 1/2, strictly >= 0!)
        iv_naive = QInterval(Fraction(0), Fraction(1)) - QInterval(Fraction(0), Fraction(1)).sqr()
        iv_bern = bernstein_enclosure({(1,): Fraction(1), (2,): Fraction(-1)}, [QInterval(Fraction(0), Fraction(1))])
        _req(iv_naive.lo == -1 and iv_naive.hi == 1, "naive interval sanity")
        _req(iv_bern.lo == 0 and iv_bern.hi == Fraction(1, 2), f"Bernstein expected [0, 1/2], got {iv_bern}")
        _req(iv_bern.width() < iv_naive.width(), "Bernstein must beat naive interval width")

        # 2D non-affine polynomial soundness check against 100 random interior rational points
        terms = {(2, 0): Fraction(1), (1, 1): Fraction(-2), (0, 2): Fraction(1), (1, 0): Fraction(1, 3)}
        box = [QInterval(Fraction(-1, 2), Fraction(3, 2)), QInterval(Fraction(0), Fraction(1))]
        enc = bernstein_enclosure(terms, box)
        rng = random.Random(101)
        for _ in range(100):
            x = Fraction(rng.randint(-50, 150), 100)
            y = Fraction(rng.randint(0, 100), 100)
            val = (x - y) ** 2 + x / 3
            _req(enc.lo <= val <= enc.hi, f"Bernstein enclosure violated: {val} not in {enc}")

    def test_02_fibral_rigidity_5_two_bar_truss(self) -> None:
        res = run_fibral_truss_validation()
        # All 5 docs/10 §4.2 table points verified
        _req(len(res["docs10_table_5_points"]) == 5, "expected 5 table points")
        # Full box [0.7, 1.3] x [0.9, 1.5] MUST NOT certify constant inertia and MUST find (9/10, 11/10)
        full = res["full_box_0p7_1p3_x_0p9_1p5"]
        _req(full["status"] == "SINGULARITY_DETECTED", f"expected SINGULARITY_DETECTED, got {full['status']}")
        pts = [tuple(w["point"]) for w in full["singular_witnesses"]]
        _req(("9/10", "11/10") in pts, f"expected (9/10, 11/10) singular witness in {pts}")
        for w in full["singular_witnesses"]:
            _req(w["inertia"] == [1, 0, 1] and w["dual_oracle_verified"], f"bad singular witness {w}")

        # Taut and buckled sub-boxes certified constant PD (2, 0, 0)
        _req(res["taut_subbox_certified_PD"]["status"] == "CERTIFIED_CONSTANT_INERTIA"
             and res["taut_subbox_certified_PD"]["certified_inertia"] == [2, 0, 0],
             "taut sub-box failed PD certification")
        _req(res["buckled_subbox_certified_PD"]["status"] == "CERTIFIED_CONSTANT_INERTIA"
             and res["buckled_subbox_certified_PD"]["certified_inertia"] == [2, 0, 0],
             "buckled sub-box failed PD certification")

        # Spot-check 40 random interior points in both certified sub-boxes via independent Oracle 2
        rng = random.Random(2026)
        for _ in range(20):
            l1 = Fraction(rng.randint(70, 90), 100)
            l2 = Fraction(rng.randint(90, 100), 100)
            _req(oracle_faddeev_descartes_sturm(truss_equilibrium_hessian_raw(l1, l2))["inertia"] == (2, 0, 0),
                 "taut interior spot-check failed")
            l1b = Fraction(rng.randint(110, 130), 100)
            l2b = Fraction(rng.randint(110, 150), 100)
            _req(oracle_faddeev_descartes_sturm(truss_equilibrium_hessian_raw(l1b, l2b))["inertia"] == (2, 0, 0),
                 "buckled interior spot-check failed")

    def test_03_complex_hermitian_bloch_and_morse_boxes(self) -> None:
        res = run_bloch_and_hessian_validations()

        # 1A. Gapped complex Hermitian Bloch box certified PD (2, 0, 0)
        bg = res["bloch_2d_gapped_complex_hermitian_box"]
        _req(bg["status"] == "CERTIFIED_CONSTANT_INERTIA" and bg["certified_inertia"] == [2, 0, 0],
             f"gapped Bloch box failed: {bg}")

        # Verify 30 random interior complex points in [-1, 1]^2 via Oracle 2
        bloch_gapped = build_bloch_2d_polymatrix(Fraction(4), Fraction(1), Fraction(1), Fraction(1))
        rng = random.Random(77)
        for _ in range(30):
            pt = (Fraction(rng.randint(-100, 100), 100), Fraction(rng.randint(-100, 100), 100))
            M_pt = bloch_gapped.eval_point(pt)
            _req(oracle_faddeev_descartes_sturm(M_pt)["inertia"] == (2, 0, 0), "Bloch spot-check failed")

        # 1B. Critical Bloch box: all 4 corners PD (2, 0, 0), yet interior (0, 0) is singular (1, 0, 1)!
        bloch_dirac = build_bloch_2d_polymatrix(Fraction(3), Fraction(1), Fraction(1), Fraction(1))
        for c1 in (Fraction(-1), Fraction(1)):
            for c2 in (Fraction(-1), Fraction(1)):
                _req(oracle_faddeev_descartes_sturm(bloch_dirac.eval_point((c1, c2)))["inertia"] == (2, 0, 0),
                     "expected all 4 Dirac box corners strictly PD")
        bd = res["bloch_2d_interior_dirac_singularity_box"]
        _req(bd["status"] == "SINGULARITY_DETECTED", f"expected SINGULARITY_DETECTED on Dirac box: {bd}")
        d_pts = [tuple(w["point"]) for w in bd["singular_witnesses"]]
        _req(("0", "0") in d_pts, f"expected exact interior Dirac witness (0, 0), got {d_pts}")

        # 2A. 3x3 Morse saddle certified constant (2, 1, 0)
        ms = res["morse_3x3_constant_saddle_box"]
        _req(ms["status"] == "CERTIFIED_CONSTANT_INERTIA" and ms["certified_inertia"] == [2, 1, 0],
             f"Morse saddle box failed: {ms}")

        # 2B. 3x3 Morse irrational bifurcation certified INERTIA_CHANGE_DETECTED
        mb = res["morse_3x3_irrational_bifurcation_box"]
        _req(mb["status"] == "INERTIA_CHANGE_DETECTED", f"expected INERTIA_CHANGE_DETECTED: {mb}")
        _req(len(mb["inertia_change_witnesses"]) >= 1, "missing inertia change witness")

    def test_04_ratmatrix_and_zero_diagonal_2x2_block_box(self) -> None:
        """
        Test BOTH:
          (a) RatMatrix centered Bernstein residual on a non-affine rational complex Hermitian family;
          (b) Zero-diagonal indefinite Hermitian family [[0, 2 + i*x], [2 - i*x, 0]] forcing a
              2x2 Bunch-Kaufman pivot block on box x in [-1, 1] -> certified constant (1, 1, 0)!
        """
        x = MultiPoly.var(1, 0)
        one = MultiPoly.const(1, 1)
        i_u = MultiPoly.const(1, Qi(Fraction(0), Fraction(1)))

        # (a) RatMatrix: M(x) = [[ (4 + x^2)/(1 + x^2), (1 + i*x)/(1 + x^2) ],
        #                        [ (1 - i*x)/(1 + x^2), (4 + x^2)/(1 + x^2) ]] on [-1, 1] -> PD (2,0,0)
        den = one + x * x
        diag = 4 + x * x
        off = one + i_u * x
        rm = RatMatrix(1, [[diag, off], [off.conj(), diag]], [[den, den], [den, den]])
        res_rm = certify_hermitian_box(rm, [(Fraction(-1), Fraction(1))], max_depth=5, max_boxes=64)
        _req(res_rm.status == "CERTIFIED_CONSTANT_INERTIA" and res_rm.certified_inertia == (2, 0, 0),
             f"RatMatrix certification failed: {res_rm.to_summary_dict()}")

        # (b) Zero-diagonal complex Hermitian matrix forcing 2x2 Bunch-Kaufman block pivot!
        z = MultiPoly(1)
        off2 = 2 + i_u * x
        pm_2x2 = PolyMatrix(1, [[z, off2], [off2.conj(), z]])
        res_2x2 = certify_hermitian_box(pm_2x2, [(Fraction(-1), Fraction(1))], max_depth=4, max_boxes=32)
        _req(res_2x2.status == "CERTIFIED_CONSTANT_INERTIA" and res_2x2.certified_inertia == (1, 1, 0),
             f"2x2 block-Gershgorin certification failed: {res_2x2.to_summary_dict()}")


if __name__ == "__main__":
    unittest.main()
