"""
Track B Validation 1: aska-physical/fibral-rigidity#5 Two-Bar Non-Affine Truss Box.

Model (matching loom#7 docs/10 §4.1–4.2 to every exact numerator/denominator):
  Pins at (-1, 0) and (1, 0), natural bar lengths (L1, L2) in box [7/10, 13/10] x [9/10, 15/10].
  - At ALL 4 corners: Hessian is strictly PD with exact inertia (2, 0, 0).
  - Along the entire interior bifurcation line L1 + L2 = 2 (including (9/10, 11/10) and (1, 1)):
    Hessian is EXACTLY singular with inertia (1, 0, 1)!
  - Proves corner tests are unsound for non-affine families, certifies constant PD (2, 0, 0) on
    disjoint sub-boxes strictly away from L1 + L2 = 2, and isolates exact rational singular
    witnesses including (9/10, 11/10) verified by Track C's dual-oracle checker!
"""
from __future__ import annotations

from fractions import Fraction
import json
from typing import Any

from ..box_certifier import (
    Box,
    IntervalCMat,
    QInterval,
    QiInterval,
    certify_hermitian_box,
)
from ..dual_oracle import oracle_faddeev_descartes_sturm, produce_c_certificate, verify_congruence_c_cert
from ..exact_qi import CMat, Qi, ZERO, frac_to_str, require_cert


def truss_equilibrium_hessian_congruent(L1: Fraction, L2: Fraction) -> CMat:
    """
    Exact rational equilibrium Hessian in inertia-preserving coordinates:
      - On-line regime (L1 + L2 <= 2, y = 0): exact raw Hessian
          H = diag((L1+L2)/(L1*L2), (L1+L2)/(L1*L2)*(1 - (L1+L2)/2)).
      - Off-line regime (L1 + L2 > 2, |L1 - L2| < 2, y^2 > 0): exact rational congruent matrix
          diag(1, 1/y) * H_raw * diag(1, 1/y) = [[A, B], [B, C]],
        which has IDENTICAL Sylvester inertia to H_raw by Sylvester's law of inertia.
    """
    if L1 + L2 <= 2:
        a = (L1 + L2) / (L1 * L2)
        c = a * (Fraction(1) - (L1 + L2) / 2)
        return [[Qi(a), ZERO], [ZERO, Qi(c)]]
    x = (L1 * L1 - L2 * L2) / 4
    A = ((1 + x) ** 2) / (L1 ** 3) + ((x - 1) ** 2) / (L2 ** 3)
    B = (1 + x) / (L1 ** 3) + (x - 1) / (L2 ** 3)
    C = Fraction(1) / (L1 ** 3) + Fraction(1) / (L2 ** 3)
    return [[Qi(A), Qi(B)], [Qi(B), Qi(C)]]


# Backward-compatible alias
truss_equilibrium_hessian_raw = truss_equilibrium_hessian_congruent


def truss_interval_box(box: Box) -> IntervalCMat:
    """
    Exact coordinate-consistent QInterval enclosure over box [L1_lo, L1_hi] x [L2_lo, L2_hi]:
      - Strictly inside L1 + L2 < 2: exact interval enclosure of on-line diag Hessian.
      - Strictly inside L1 + L2 > 2: exact interval enclosure of congruent [[A, B], [B, C]]
        (valid because y^2 > 0 uniformly on the sub-box, so diag(1, 1/y) is nonsingular everywhere).
      - Straddling L1 + L2 = 2: raises CertError("REGIME_BOUNDARY_SUBDIVIDE", ...) so the box
        certifier NEVER mixes on-line and congruent coordinates and MUST subdivide / probe the
        bifurcation line L1 + L2 = 2!
    """
    L1, L2 = box[0], box[1]
    s = L1 + L2

    if s.hi < 2:
        a_iv = (L1 + L2) / (L1 * L2)
        c_iv = a_iv * (QInterval.pt(1) - (L1 + L2) / 2)
        return [
            [QiInterval(a_iv), QiInterval.pt(0)],
            [QiInterval.pt(0), QiInterval(c_iv)],
        ]

    if s.lo > 2:
        diff = L1 - L2
        y2_iv = (s.sqr() - 4) * (QInterval.pt(4) - diff.sqr()) / 16
        require_cert(y2_iv.lo > 0, "TRUSS_Y2_NONPOS", "off-line box must keep y^2 > 0")
        x_iv = (L1.sqr() - L2.sqr()) / 4
        L1_3 = L1.pow_int(3)
        L2_3 = L2.pow_int(3)
        A_iv = (x_iv + 1).sqr() / L1_3 + (x_iv - 1).sqr() / L2_3
        B_iv = (x_iv + 1) / L1_3 + (x_iv - 1) / L2_3
        C_iv = QInterval.pt(1) / L1_3 + QInterval.pt(1) / L2_3
        return [
            [QiInterval(A_iv), QiInterval(B_iv)],
            [QiInterval(B_iv), QiInterval(C_iv)],
        ]

    from ..exact_qi import CertError
    raise CertError("REGIME_BOUNDARY_SUBDIVIDE", "box straddles bifurcation line L1 + L2 = 2; subdivide")


def truss_singular_probe(sub: Box) -> list[tuple[Fraction, ...]]:
    """
    Exact rational probe on any sub-box straddling the bifurcation line L1 + L2 = 2:
    checks canonical rational witness (9/10, 11/10) if inside sub, plus the exact
    rational midpoint of the intersection segment {(L1, 2 - L1)} cap sub!
    """
    L1, L2 = sub[0], sub[1]
    if (L1.lo + L2.lo) <= 2 <= (L1.hi + L2.hi):
        pts: list[tuple[Fraction, ...]] = []
        canon = (Fraction(9, 10), Fraction(11, 10))
        if L1.lo <= canon[0] <= L1.hi and L2.lo <= canon[1] <= L2.hi:
            pts.append(canon)
        # Exact intersection interval for L1 on L1 + L2 = 2: L1 in [max(L1.lo, 2-L2.hi), min(L1.hi, 2-L2.lo)]
        lo_1 = max(L1.lo, Fraction(2) - L2.hi)
        hi_1 = min(L1.hi, Fraction(2) - L2.lo)
        if lo_1 <= hi_1:
            m1 = (lo_1 + hi_1) / 2
            pts.append((m1, Fraction(2) - m1))
        return pts
    return []


def run_fibral_truss_validation() -> dict[str, Any]:
    """
    Full exact validation of aska-physical/fibral-rigidity#5:
      1. Verify all 5 exact matrices from loom#7 docs/10 §4.2 table (4 PD corners + singular (9/10, 11/10)).
      2. Run Track B box certifier on full box [7/10, 13/10] x [9/10, 15/10] -> detects interior
         singularity and isolates exact rational witness (9/10, 11/10) with inertia (1, 0, 1).
      3. Run Track B box certifier on strictly taut sub-box [7/10, 9/10] x [9/10, 1] ->
         CERTIFIED_CONSTANT_INERTIA (2, 0, 0) everywhere!
      4. Run Track B box certifier on strictly buckled sub-box [11/10, 13/10] x [11/10, 15/10] ->
         CERTIFIED_CONSTANT_INERTIA (2, 0, 0) everywhere!
    """
    table_pts = [
        ("corner_1", Fraction(7, 10), Fraction(9, 10), (2, 0, 0)),
        ("corner_2", Fraction(7, 10), Fraction(3, 2), (2, 0, 0)),
        ("corner_3", Fraction(13, 10), Fraction(9, 10), (2, 0, 0)),
        ("corner_4", Fraction(13, 10), Fraction(3, 2), (2, 0, 0)),
        ("interior_singular", Fraction(9, 10), Fraction(11, 10), (1, 0, 1)),
    ]
    point_checks = []
    for label, l1, l2, expected in table_pts:
        M = truss_equilibrium_hessian_raw(l1, l2)
        C, C_inv, D, in1 = produce_c_certificate(M)
        verify_congruence_c_cert(M, C, C_inv, D, claim=list(expected))
        o2 = oracle_faddeev_descartes_sturm(M)
        require_cert(o2["inertia"] == expected, "TRUSS_TABLE_MISMATCH", f"{label}: {o2['inertia']} != {expected}")
        point_checks.append({
            "label": label,
            "L1": frac_to_str(l1),
            "L2": frac_to_str(l2),
            "inertia": list(expected),
            "M": [[frac_to_str(v.re) for v in row] for row in M],
        })

    # Full non-affine box [0.7, 1.3] x [0.9, 1.5]
    full_res = certify_hermitian_box(
        lambda pt: truss_equilibrium_hessian_raw(pt[0], pt[1]),
        [(Fraction(7, 10), Fraction(13, 10)), (Fraction(9, 10), Fraction(15, 10))],
        eval_box_fn=truss_interval_box,
        max_depth=6,
        max_boxes=256,
        singular_probe_fn=truss_singular_probe,
    )

    # Purely taut sub-box [0.7, 0.9] x [0.9, 1.0] (L1+L2 in [1.6, 1.9] < 2)
    taut_res = certify_hermitian_box(
        lambda pt: truss_equilibrium_hessian_raw(pt[0], pt[1]),
        [(Fraction(7, 10), Fraction(9, 10)), (Fraction(9, 10), Fraction(1))],
        eval_box_fn=truss_interval_box,
        max_depth=6,
        max_boxes=64,
    )

    # Purely buckled sub-box [1.1, 1.3] x [1.1, 1.5] (L1+L2 in [2.2, 2.8] > 2)
    buckled_res = certify_hermitian_box(
        lambda pt: truss_equilibrium_hessian_raw(pt[0], pt[1]),
        [(Fraction(11, 10), Fraction(13, 10)), (Fraction(11, 10), Fraction(15, 10))],
        eval_box_fn=truss_interval_box,
        max_depth=6,
        max_boxes=128,
    )

    return {
        "docs10_table_5_points": point_checks,
        "full_box_0p7_1p3_x_0p9_1p5": full_res.to_summary_dict(),
        "taut_subbox_certified_PD": taut_res.to_summary_dict(),
        "buckled_subbox_certified_PD": buckled_res.to_summary_dict(),
    }


if __name__ == "__main__":
    print(json.dumps(run_fibral_truss_validation(), indent=2))
