"""
Track B Validations 2 & 3:
  2. Complex Hermitian 2D Bloch Dynamical Matrix over Continuous Wavevector Boxes
     (using exact rational Weierstrass substitution e^{i q_k} = (1 - t_k^2 + 2 i t_k) / (1 + t_k^2),
      ready for @fractals-probe's incentre-lattices continuous Bloch/fold boxes!).
  3. Indefinite Non-Affine 3x3 Morse-Index Hessian Box
     (ready for @gravity-probe's relative-equilibria / point-charges / gravity Hessians!):
     - Certifies constant saddle Morse index (2, 1, 0) on a safe continuous box.
     - Detects interior inertia flip (2, 1, 0) <-> (1, 2, 0) and exact rational singular
       bifurcation point on a box crossing det H(x, y) = 0.
"""
from __future__ import annotations

from fractions import Fraction
import json
from typing import Any

from ..box_certifier import (
    Box,
    MultiPoly,
    PolyMatrix,
    certify_hermitian_box,
)
from ..exact_qi import ONE, Qi


def build_bloch_2d_polymatrix(
    m_diag: Fraction,
    a_hop: Fraction,
    b_hop: Fraction,
    c_hop: Fraction,
) -> PolyMatrix:
    """
    Build exact Q(i)[t1, t2] complex Hermitian polynomial matrix W(t1, t2) * D(t1, t2),
    where W(t1, t2) = (1 + t1^2)(1 + t2^2) > 0 everywhere on R^2 and
      D(t1, t2) = [[ m,                      a + b e^{i q1} + c e^{i q2} ],
                   [ a + b e^{-i q1} + c e^{-i q2},  m                   ]]
    with exact Weierstrass map e^{i q_k} = (1 - t_k^2 + 2 i t_k) / (1 + t_k^2).
    Because W(t1, t2) > 0 strictly for all (t1, t2) in R^2, W * D has the EXACT SAME
    Sylvester inertia as D(q1, q2) at every real wavevector!
    """
    t1 = MultiPoly.var(2, 0)
    t2 = MultiPoly.var(2, 1)
    one = MultiPoly.const(2, 1)
    i_unit = MultiPoly.const(2, Qi(Fraction(0), Fraction(1)))

    w1 = one + t1 * t1
    w2 = one + t2 * t2
    W = w1 * w2

    # Numerators of e^{i q1} and e^{i q2}: z_k = (1 - t_k^2) + 2 i t_k
    z1 = (one - t1 * t1) + (2 * i_unit) * t1
    z2 = (one - t2 * t2) + (2 * i_unit) * t2

    # W * (a + b e^{iq1} + c e^{iq2}) = a * w1 * w2 + b * z1 * w2 + c * w1 * z2
    off = (a_hop * W) + (b_hop * (z1 * w2)) + (c_hop * (w1 * z2))
    diag = m_diag * W
    return PolyMatrix(2, [[diag, off], [off.conj(), diag]])


def build_morse_3x3_polymatrix() -> PolyMatrix:
    """
    Non-affine 3x3 real symmetric Hessian family H(x, y):
      H(x, y) = [[ 2 + x^2,   x*y,       0       ],
                 [ x*y,       y^2 - 1,   x - y   ],
                 [ 0,         x - y,     3 + y^2 ]]
    Notice:
      - At (x, y) = (0, 0): H = diag(2, -1, 3) -> indefinite saddle Morse index (2, 1, 0)!
      - At (x, y) = (0, 1): H = [[2, 0, 0], [0, 0, -1], [0, -1, 4]] -> det = -2 < 0 -> (2, 1, 0).
      - At (x, y) = (0, 2): H = [[2, 0, 0], [0, 3, -2], [0, -2, 7]] -> det = 2*(21-4) = 34 > 0 -> PD (3, 0, 0)!
      - Exact interior transition where det H(x, y) = 0 occurs between y=1 and y=2!
        Specifically along x = 0: det H(0, y) = 2 * ((y^2 - 1)(3 + y^2) - y^2) = 2 * (y^4 + y^2 - 3).
        And along x = y: H(t, t) = [[2+t^2, t^2, 0], [t^2, t^2-1, 0], [0, 0, 3+t^2]],
        whose det is (3+t^2)*((2+t^2)(t^2-1) - t^4) = (3+t^2)*(t^2 - 2) -> vanishes at t = sqrt(2),
        and at (x, y) = (1, 1): det = 4*(3*0 - 1) = -4 < 0 (inertia (2,1,0)),
        at (x, y) = (2, 2): det = 7*(6*3 - 16) = +14 > 0 (inertia (3,0,0))!
        Even nicer: shift the (1,1) entry to y^2 - 2 -> along x = y = 1: wait, let's check
        det H_shifted(t, t) = (3+t^2)*((2+t^2)(t^2-2) - t^4) = -4(3+t^2) < 0.
        Instead, keep H(x, y) clean as above and note it also has an exact rational zero at
        (x, y) = (0, 1) if we adjust (2,2) or let's pick a clean rational singular point!
    Let's use:
      H(x, y) = [[ 2 + x^2,   x*y,       0       ],
                 [ x*y,       y^2 - 1,   x - 1   ],
                 [ 0,         x - 1,     3 + y^2 ]]
      Check at (x, y) = (1, 1): H = [[3, 1, 0], [1, 0, 0], [0, 0, 4]] -> det = -4 -> (2, 1, 0).
      Check at (x, y) = (0, 0): H = [[2, 0, 0], [0, -1, -1], [0, -1, 3]] -> det = 2*(-3-1) = -8 -> (2, 1, 0).
      Check at (x, y) = (1, 2): H = [[3, 2, 0], [2, 3, 0], [0, 0, 7]] -> det = 7*(9-4) = 35 -> (3, 0, 0)!
      Check at (x, y) = (1, 3/2): H = [[3, 3/2, 0], [3/2, 5/4, 0], [0, 0, 21/4]] -> det = 3*5/4 - 9/4 = 6/4 > 0 -> (3,0,0).
      Check exact rational zero along x = 1: (3)(y^2 - 1) - y^2 = 2 y^2 - 3 = 0 (irrational sqrt(3/2)!).
      GREAT! That tests BOTH:
        - Uniform saddle (2, 1, 0) certification on [-1/2, 1/2] x [-1/2, 1/2], AND
        - Certified INERTIA_CHANGE_DETECTED (2, 1, 0) <-> (3, 0, 0) across an IRRATIONAL bifurcation curve!
    """
    x = MultiPoly.var(2, 0)
    y = MultiPoly.var(2, 1)
    z = MultiPoly(2)
    h00 = 2 + x * x
    h01 = x * y
    h11 = y * y - 1
    h12 = x - 1
    h22 = 3 + y * y
    return PolyMatrix(
        2,
        [
            [h00, h01, z],
            [h01, h11, h12],
            [z, h12, h22],
        ],
    )


def run_bloch_and_hessian_validations() -> dict[str, Any]:
    # 1A. Gapped complex Hermitian Bloch box: m=4, a=1, b=1, c=1 -> |a + b e^{iq1} + c e^{iq2}| <= 3 < 4
    # Strictly PD (2, 0, 0) across ENTIRE continuous 2D wavevector box t1, t2 in [-1, 1] x [-1, 1]!
    bloch_gapped = build_bloch_2d_polymatrix(Fraction(4), Fraction(1), Fraction(1), Fraction(1))
    res_bloch_gapped = certify_hermitian_box(
        bloch_gapped,
        [(Fraction(-1), Fraction(1)), (Fraction(-1), Fraction(1))],
        max_depth=6,
        max_boxes=128,
    )

    # 1B. Critical complex Hermitian Bloch box with interior Dirac zero mode!
    # Take m = 3, a = 1, b = 1, c = 1:
    # At (t1, t2) = (0, 0) (q = (0, 0)): off-diag = 1 + 1 + 1 = 3 == m -> EXACT SINGULAR (1, 0, 1)!
    # At ALL 4 corners of [-1, 1] x [-1, 1]: e^{i q_k} = +-i, so |1 +- i +- i| in {1, sqrt(5)} < 3 ->
    # ALL 4 CORNERS ARE STRICTLY PD (2, 0, 0), YET THE INTERIOR (0, 0) IS EXACTLY SINGULAR (1, 0, 1)!!
    bloch_dirac = build_bloch_2d_polymatrix(Fraction(3), Fraction(1), Fraction(1), Fraction(1))
    res_bloch_dirac = certify_hermitian_box(
        bloch_dirac,
        [(Fraction(-1), Fraction(1)), (Fraction(-1), Fraction(1))],
        max_depth=5,
        max_boxes=128,
    )

    # 2A. Non-affine 3x3 Morse Hessian on safe saddle box [-1/2, 1/2] x [-1/2, 1/2] -> constant (2, 1, 0)!
    morse_H = build_morse_3x3_polymatrix()
    res_morse_saddle = certify_hermitian_box(
        morse_H,
        [(Fraction(-1, 2), Fraction(1, 2)), (Fraction(-1, 2), Fraction(1, 2))],
        max_depth=6,
        max_boxes=128,
    )

    # 2B. Non-affine 3x3 Morse Hessian crossing irrational bifurcation curve on [1/2, 3/2] x [1/2, 2] ->
    # certifies INERTIA_CHANGE_DETECTED between (2, 1, 0) and (3, 0, 0)!
    res_morse_bif = certify_hermitian_box(
        morse_H,
        [(Fraction(1, 2), Fraction(3, 2)), (Fraction(1, 2), Fraction(2))],
        max_depth=5,
        max_boxes=128,
    )

    return {
        "bloch_2d_gapped_complex_hermitian_box": res_bloch_gapped.to_summary_dict(),
        "bloch_2d_interior_dirac_singularity_box": res_bloch_dirac.to_summary_dict(),
        "morse_3x3_constant_saddle_box": res_morse_saddle.to_summary_dict(),
        "morse_3x3_irrational_bifurcation_box": res_morse_bif.to_summary_dict(),
    }


if __name__ == "__main__":
    print(json.dumps(run_bloch_and_hessian_validations(), indent=2))
