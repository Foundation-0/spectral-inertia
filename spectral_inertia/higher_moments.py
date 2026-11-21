"""
Track A (SEAM-01): Complete R_opt + Higher-Moment Exact-Rational Spectral Rank Bounds.

Every theorem below bounds the STRICTLY STRONGER projected positive inertia chain
for ALL non-commuting complex Hermitian matrices H = P + Q (P >= 0, n_+(Q) <= b, W = range(Q_+)):

    rank(P) >= rank(Pi_{W^perp} P Pi_{W^perp}) >= n_+(Pi_{W^perp} H Pi_{W^perp}) >= BOUND.

Four exact-rational theorem families (zero floats in any TCB certifier, zero bare asserts):
  - Theorem A1: Guarded sharp quadratic envelope R_opt(u, t, S, b) (with exact 6-term slack).
  - Theorem A2: Degree-2m Stieltjes-Hankel indefinite spectral rank bound R_{H,2m}(H, b)
                (closed-form quartic R_H4 + exact active-set KKT sextic R_H6 + general 2m certifier).
  - Theorem A3: Exact Noise-Annihilating Quartic SOS bound Phi_{x0, tau}(H) - b
                (double zero at lambda = -tau, closed-form rational SOS certificate 1 - Phi >= 0,
                 specializes at tau=0 to exact indefinite odd-even Holder S_3^4 / S_4^3 - b).
  - Theorem A4: Exact Weighted Quartic-Weyl SOS bound R_{W4}(S_1..S_4, tr(Q), tr(Q^3), b)
                (5-parameter general SOS + 3-parameter peak-matched closed form using only tr(Q)).
"""
from __future__ import annotations

from fractions import Fraction
import math
from typing import Any, Sequence

from .exact_qi import (
    CMat,
    CertError,
    cmat_mul,
    cmat_trace_real,
    frac_to_str,
    is_hermitian,
    parse_strict_fraction,
    parse_strict_int,
    require_cert,
)


# ==============================================================================
# EXACT SPECTRAL MOMENTS S_k = tr(H^k) OVER Q(i)
# ==============================================================================
def spectral_moments_exact(H: CMat, max_k: int = 6) -> dict[int, Fraction]:
    """Compute exact rational spectral moments S_k = tr(H^k) for k = 1..max_k."""
    require_cert(is_hermitian(H), "MATRIX_NOT_HERMITIAN", "spectral_moments requires Hermitian H")
    k_max = parse_strict_int(max_k, min_value=1, max_value=12)
    moments: dict[int, Fraction] = {}
    Hk = H
    moments[1] = cmat_trace_real(Hk)
    for k in range(2, k_max + 1):
        Hk = cmat_mul(Hk, H)
        moments[k] = cmat_trace_real(Hk)
    return moments


# ==============================================================================
# THEOREM A1: GUARDED SHARP QUADRATIC ENVELOPE R_opt (+ BASELINES R_G, LEMMA 3.2)
# ==============================================================================
def R_opt(u: Fraction, t: Fraction, S: Fraction, b: int) -> Fraction:
    """
    Theorem A1 (Guarded Sharp Projected Envelope):
      - Guard 1: if u <= 0 or u + t <= 0 -> 0 (prevents 0/0 at u=0, t^2=bS).
      - Regime 1: if b > 0 and t > 0 and t*(u+t) >= b*S -> u^2 / (S - t^2/b).
      - Regime 2 (Guard 2): max(0, (u+t)^2 / S - b).
    """
    u_f = parse_strict_fraction(u)
    t_f = parse_strict_fraction(t)
    S_f = parse_strict_fraction(S)
    b_i = parse_strict_int(b, min_value=0)
    if u_f <= 0 or (u_f + t_f) <= 0:
        return Fraction(0)
    require_cert(S_f > 0, "INVALID_FROB_NORM", "S = ||H||_F^2 must be > 0 when u + t > 0")
    if b_i > 0 and t_f > 0 and t_f * (u_f + t_f) >= Fraction(b_i) * S_f:
        denom = S_f - (t_f * t_f) / Fraction(b_i)
        require_cert(denom > 0, "INFEASIBLE_MOMENTS", "feasible u>0, t>0 requires S > t^2/b")
        return (u_f * u_f) / denom
    val = ((u_f + t_f) * (u_f + t_f)) / S_f - Fraction(b_i)
    return val if val > 0 else Fraction(0)


def R_G_fable(u: Fraction, t: Fraction, S: Fraction, b: int) -> Fraction:
    """Fable's loom#7 docs/10 §3.3 best unscaled family member R_G (baseline)."""
    u_f = parse_strict_fraction(u)
    t_f = parse_strict_fraction(t)
    S_f = parse_strict_fraction(S)
    b_i = parse_strict_int(b, min_value=0)
    if b_i > 0 and t_f >= Fraction(b_i):
        return 2 * u_f + (t_f * t_f) / Fraction(b_i) - S_f
    return 2 * (u_f + t_f) - S_f - Fraction(b_i)


def R_lemma32_fixed_c(u: Fraction, t: Fraction, S: Fraction, b: int, c: Fraction = Fraction(2)) -> Fraction:
    """Scale-optimized Lemma 3.2 at fixed weight c >= 1 (baseline)."""
    u_f = parse_strict_fraction(u)
    t_f = parse_strict_fraction(t)
    S_f = parse_strict_fraction(S)
    b_i = parse_strict_int(b, min_value=0)
    c_f = parse_strict_fraction(c)
    require_cert(c_f >= 1, "INVALID_WEIGHT_C", "Lemma 3.2 requires c >= 1")
    Tc = u_f + c_f * t_f
    if u_f <= 0 or Tc <= 0 or S_f <= 0:
        return Fraction(0)
    val = (Tc * Tc) / S_f - c_f * c_f * Fraction(b_i)
    return val if val > 0 else Fraction(0)


# ==============================================================================
# THEOREM A2: DEGREE-2m STIELTJES-HANKEL INDEFINITE PROJECTED-INERTIA BOUND
# ==============================================================================
def certify_stieltjes_hankel_2m(
    moments: dict[int, Fraction],
    b: int,
    a_coeffs: Sequence[Any],
) -> dict[str, Any]:
    """
    Exact rational TCB verifier for Theorem A2 (Degree-2m Stieltjes-Hankel bound):
      Given witness a = (a_1, ..., a_m) with ALL a_k >= 0:
        q_a(lam) = 1 + sum_{k=1}^m (-1)^k a_k lam^k
        phi_a(lam) = 1 - q_a(lam)^2
      For all lam <= 0: q_a(lam) = 1 + sum a_k |lam|^k >= 1 => phi_a(lam) <= 0.
      For all lam > 0:  phi_a(lam) <= 1.
      Hence n_+(Pi_{W^perp} H Pi_{W^perp}) >= n_+(H) - b >= tr(phi_a(H)) - b.
    """
    b_i = parse_strict_int(b, min_value=0)
    if not isinstance(a_coeffs, (list, tuple)) or len(a_coeffs) == 0:
        raise CertError("EMPTY_HANKEL_WITNESS", "a_coeffs must be non-empty")
    m = len(a_coeffs)
    a = [parse_strict_fraction(v) for v in a_coeffs]
    for idx, ak in enumerate(a, start=1):
        require_cert(ak >= 0, "NEGATIVE_HANKEL_COEFF", f"a_{idx} = {ak} < 0 violates phi(lam)<=0 on lam<=0")
    for k in range(1, 2 * m + 1):
        require_cert(k in moments, "MISSING_SPECTRAL_MOMENT", f"moment S_{k} required for degree {2*m}")
        parse_strict_fraction(moments[k])

    # tr(1 - q_a(H)^2) = 2 * sum_{k=1}^m (-1)^{k-1} a_k S_k - sum_{j,k=1}^m (-1)^{j+k} a_j a_k S_{j+k}
    lin = Fraction(0)
    for k in range(1, m + 1):
        sign = Fraction(1) if ((k - 1) % 2 == 0) else Fraction(-1)
        lin += sign * a[k - 1] * moments[k]
    quad = Fraction(0)
    for j in range(1, m + 1):
        for k in range(1, m + 1):
            sign = Fraction(1) if ((j + k) % 2 == 0) else Fraction(-1)
            quad += sign * a[j - 1] * a[k - 1] * moments[j + k]

    tr_phi = 2 * lin - quad
    raw = tr_phi - Fraction(b_i)
    bound = raw if raw > 0 else Fraction(0)
    return {
        "theorem": f"A2_Stieltjes_Hankel_deg{2*m}",
        "degree": 2 * m,
        "b": b_i,
        "witness_a": [frac_to_str(x) for x in a],
        "tr_phi_H": frac_to_str(tr_phi),
        "exact_bound": bound,
        "exact_bound_str": frac_to_str(bound),
    }


def R_hankel4_exact(S1: Fraction, S2: Fraction, S3: Fraction, S4: Fraction, b: int = 0) -> dict[str, Any]:
    """
    Closed-form exact rational KKT global optimum of Theorem A2 at degree 4 (m = 2):
      max_{s >= 0, p >= 0} [2 s S1 - 2 p S2 - s^2 S2 + 2 s p S3 - p^2 S4] - b.
    When Delta = S2*S4 - S3^2 > 0, s* >= 0, p* >= 0:
      R_H4 = S1^2/S2 + (S1*S3 - S2^2)^2 / (S2*(S2*S4 - S3^2)) - b.
    """
    s1 = parse_strict_fraction(S1)
    s2 = parse_strict_fraction(S2)
    s3 = parse_strict_fraction(S3)
    s4 = parse_strict_fraction(S4)
    b_i = parse_strict_int(b, min_value=0)
    moments = {1: s1, 2: s2, 3: s3, 4: s4}

    candidates: list[tuple[Fraction, Fraction]] = [(Fraction(0), Fraction(0))]
    # Boundary p = 0, s = max(0, S1/S2)
    if s2 > 0 and s1 > 0:
        candidates.append((s1 / s2, Fraction(0)))
    # Interior KKT stationary point
    det = s2 * s4 - s3 * s3
    if det > 0:
        s_star = (s1 * s4 - s2 * s3) / det
        p_star = (s1 * s3 - s2 * s2) / det
        if s_star >= 0 and p_star >= 0:
            candidates.append((s_star, p_star))

    best_cert: dict[str, Any] | None = None
    for cand in candidates:
        cert = certify_stieltjes_hankel_2m(moments, b_i, list(cand))
        if best_cert is None or cert["exact_bound"] > best_cert["exact_bound"]:
            best_cert = cert
    require_cert(best_cert is not None, "INTERNAL_H4_EMPTY", "no candidate evaluated")
    assert_never = best_cert  # local alias (not an assert!)
    return assert_never


def _solve_small_linear_q(A: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction] | None:
    """Exact rational Gaussian elimination for tiny k x k systems (k <= 4). Returns None if singular."""
    k = len(A)
    M = [A[i][:] + [rhs[i]] for i in range(k)]
    for col in range(k):
        piv = None
        for r in range(col, k):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            return None
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(k):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [M[r][c] - f * M[col][c] for c in range(k + 1)]
    return [M[i][k] for i in range(k)]


def R_hankel6_exact(moments: dict[int, Fraction], b: int = 0) -> dict[str, Any]:
    """
    Exact rational KKT global optimum of Theorem A2 at degree 6 (m = 3):
      max_{a_1, a_2, a_3 >= 0} [2 a^T v_tilde - a^T M_tilde a] - b.
    Evaluates ALL 2^3 = 8 active subsets in exact Fraction arithmetic -> guaranteed >= R_hankel4_exact!
    """
    b_i = parse_strict_int(b, min_value=0)
    for k in range(1, 7):
        require_cert(k in moments, "MISSING_SPECTRAL_MOMENT", f"S_{k} required for R_hankel6")
        parse_strict_fraction(moments[k])

    v_tilde = [moments[1], -moments[2], moments[3]]
    M_tilde = [
        [moments[2], -moments[3], moments[4]],
        [-moments[3], moments[4], -moments[5]],
        [moments[4], -moments[5], moments[6]],
    ]

    best_cert = certify_stieltjes_hankel_2m(moments, b_i, [Fraction(0), Fraction(0), Fraction(0)])

    for mask in range(1, 8):
        active = [idx for idx in range(3) if (mask & (1 << idx)) != 0]
        sub_M = [[M_tilde[i][j] for j in active] for i in active]
        sub_v = [v_tilde[i] for i in active]
        sol = _solve_small_linear_q(sub_M, sub_v)
        if sol is None or any(x < 0 for x in sol):
            continue
        a_full = [Fraction(0), Fraction(0), Fraction(0)]
        for pos, val in zip(active, sol):
            a_full[pos] = val
        cert = certify_stieltjes_hankel_2m(moments, b_i, a_full)
        if cert["exact_bound"] > best_cert["exact_bound"]:
            best_cert = cert

    return best_cert


# ==============================================================================
# THEOREM A3: EXACT NOISE-ANNIHILATING QUARTIC SOS BOUND Phi_{x0, tau}
# ==============================================================================
def certify_noise_annihilating_quartic(
    moments: dict[int, Fraction],
    b: int,
    x0: Any,
    tau: Any,
) -> dict[str, Any]:
    """
    Exact rational TCB verifier for Theorem A3 (Noise-Annihilating Quartic SOS Bound):
      For any rational x0 > 0 and tau >= 0:
        L = 2 x0 (2 x0 + tau) / (3 x0 + tau) > x0 > 0
        M = x0^2 (x0 + tau)^3 / (3 x0 + tau) > 0
        Phi_{x0, tau}(lam) = lam * (L - lam) * (lam + tau)^2 / M.

      Exact rational SOS certificate verified algebraically:
        M - lam(L - lam)(lam + tau)^2
          == (lam - x0)^2 * [ (lam + (x0^2 + 3 x0 tau + tau^2)/(3 x0 + tau))^2
                              + x0^2 (2 x0^2 + 4 x0 tau + tau^2) / (3 x0 + tau)^2 ] >= 0.
      And for lam <= 0: lam <= 0, L - lam > 0, (lam + tau)^2 >= 0 => Phi <= 0, with DOUBLE ZERO at -tau!
      Therefore n_+(Pi_{W^perp} H Pi_{W^perp}) >= tr(Phi_{x0, tau}(H)) - b.
    """
    b_i = parse_strict_int(b, min_value=0)
    x0_f = parse_strict_fraction(x0)
    tau_f = parse_strict_fraction(tau)
    require_cert(x0_f > 0, "INVALID_PEAK_X0", "Theorem A3 requires x0 > 0")
    require_cert(tau_f >= 0, "INVALID_TAU", "Theorem A3 requires tau >= 0")
    for k in range(1, 5):
        require_cert(k in moments, "MISSING_SPECTRAL_MOMENT", f"S_{k} required for Theorem A3")
        parse_strict_fraction(moments[k])

    denom_lin = 3 * x0_f + tau_f
    L = (2 * x0_f * (2 * x0_f + tau_f)) / denom_lin
    M = (x0_f * x0_f * ((x0_f + tau_f) ** 3)) / denom_lin
    require_cert(L > x0_f and M > 0, "INVALID_A3_DERIVED", "L > x0 and M > 0 must hold")

    # Explicit polynomial coefficient identity verification of the SOS decomposition:
    # M - [L*tau^2 lam + (2L*tau - tau^2) lam^2 + (L - 2 tau) lam^3 - lam^4]
    # == (lam - x0)^2 * (lam^2 + 2 c_shift lam + (c_shift^2 + d_pos))
    c_shift = (x0_f * x0_f + 3 * x0_f * tau_f + tau_f * tau_f) / denom_lin
    d_pos = (x0_f * x0_f * (2 * x0_f * x0_f + 4 * x0_f * tau_f + tau_f * tau_f)) / (denom_lin * denom_lin)
    require_cert(d_pos > 0, "A3_SOS_DISCRIMINANT_FAIL", "SOS positive constant d_pos must be > 0")

    b1 = 2 * c_shift
    b0 = c_shift * c_shift + d_pos
    # Expand (lam^2 - 2 x0 lam + x0^2)(lam^2 + b1 lam + b0):
    sos_c4 = Fraction(1)
    sos_c3 = b1 - 2 * x0_f
    sos_c2 = b0 - 2 * x0_f * b1 + x0_f * x0_f
    sos_c1 = -2 * x0_f * b0 + x0_f * x0_f * b1
    sos_c0 = x0_f * x0_f * b0

    # Coefficients of M - phi(lam) where phi(lam) = c1 lam + c2 lam^2 + c3 lam^3 - lam^4:
    c1 = L * tau_f * tau_f
    c2 = 2 * L * tau_f - tau_f * tau_f
    c3 = L - 2 * tau_f
    c4 = Fraction(-1)
    require_cert(
        (sos_c4, sos_c3, sos_c2, sos_c1, sos_c0) == (-c4, -c3, -c2, -c1, M),
        "A3_SOS_IDENTITY_FAIL",
        "exact polynomial SOS identity verification failed",
    )

    tr_num = c1 * moments[1] + c2 * moments[2] + c3 * moments[3] + c4 * moments[4]
    tr_phi = tr_num / M
    raw = tr_phi - Fraction(b_i)
    bound = raw if raw > 0 else Fraction(0)
    return {
        "theorem": "A3_Noise_Annihilating_Quartic_SOS",
        "b": b_i,
        "x0": frac_to_str(x0_f),
        "tau": frac_to_str(tau_f),
        "L": frac_to_str(L),
        "M": frac_to_str(M),
        "sos_verified": True,
        "tr_phi_H": frac_to_str(tr_phi),
        "exact_bound": bound,
        "exact_bound_str": frac_to_str(bound),
    }


def find_noise_quartic_witness(
    moments: dict[int, Fraction],
    b: int,
    tau: Fraction,
    *,
    x0_hints: Sequence[Fraction] | None = None,
    denom_limit: int = 10000,
) -> dict[str, Any]:
    """
    Untrusted witness proposer for Theorem A3: searches for a clean rational x0 > 0
    maximizing the exact certified bound (every candidate is strictly certified by TCB!).
    """
    b_i = parse_strict_int(b, min_value=0)
    tau_f = parse_strict_fraction(tau)
    require_cert(tau_f >= 0, "INVALID_TAU", "tau must be >= 0")

    S1f = float(moments[1])
    S2f = float(moments[2])
    S3f = float(moments[3])
    S4f = float(moments[4])
    tf = float(tau_f)

    def eval_float(x0_v: float) -> float:
        if x0_v <= 0.0:
            return -1e30
        dl = 3.0 * x0_v + tf
        L = 2.0 * x0_v * (2.0 * x0_v + tf) / dl
        M = (x0_v * x0_v * (x0_v + tf) ** 3) / dl
        if M <= 0.0:
            return -1e30
        num = (L * tf * tf) * S1f + (2.0 * L * tf - tf * tf) * S2f + (L - 2.0 * tf) * S3f - S4f
        return num / M - b_i

    # Scale estimate from S4/S3 or sqrt(S2)
    scale = 1.0
    if S3f > 0.0 and S4f > 0.0:
        scale = S4f / S3f
    elif S2f > 0.0:
        scale = math.sqrt(S2f)
    if scale <= 1e-12:
        scale = 1.0

    # Coarse log grid + golden-section refinement around best point
    best_x = scale
    best_val = eval_float(best_x)
    for k in range(-60, 61):
        cand = scale * (1.06 ** k)
        v = eval_float(cand)
        if v > best_val:
            best_val = v
            best_x = cand

    # Local golden-section refinement
    lo = best_x * 0.7
    hi = best_x * 1.4
    phi_g = (math.sqrt(5.0) - 1.0) / 2.0
    for _ in range(45):
        m1 = hi - phi_g * (hi - lo)
        m2 = lo + phi_g * (hi - lo)
        if eval_float(m1) > eval_float(m2):
            hi = m2
        else:
            lo = m1
    refined_x = 0.5 * (lo + hi)

    # Convert top candidates to exact Fractions with bounded denominator and certify via TCB!
    cand_fracs: list[Fraction] = []
    if moments[3] > 0 and moments[4] > 0:
        cand_fracs.append(moments[4] / moments[3])  # exact optimum when tau == 0!
    for xf in (best_x, refined_x):
        if xf > 0.0 and math.isfinite(xf):
            f_cand = Fraction(xf).limit_denominator(denom_limit)
            if f_cand > 0:
                cand_fracs.append(f_cand)
            f_fine = Fraction(xf).limit_denominator(denom_limit * 100)
            if f_fine > 0:
                cand_fracs.append(f_fine)
    if x0_hints:
        for h in x0_hints:
            hf = parse_strict_fraction(h)
            if hf > 0:
                cand_fracs.append(hf)
    if not cand_fracs:
        cand_fracs.append(Fraction(1))

    best_cert: dict[str, Any] | None = None
    for x_cand in cand_fracs:
        cert = certify_noise_annihilating_quartic(moments, b_i, x_cand, tau_f)
        if best_cert is None or cert["exact_bound"] > best_cert["exact_bound"]:
            best_cert = cert
    require_cert(best_cert is not None, "INTERNAL_A3_EMPTY", "no A3 witness certified")
    return best_cert


# ==============================================================================
# THEOREM A4: EXACT WEIGHTED QUARTIC-WEYL SOS BOUND R_{W4}
# ==============================================================================
def certify_weighted_quartic_weyl(
    moments_H: dict[int, Fraction],
    t1_Q: Any,
    t3_Q: Any,
    b: int,
    *,
    s: Any,
    p: Any,
    gamma1: Any,
    gamma3: Any,
    kappa: Any,
) -> dict[str, Any]:
    """
    Exact rational TCB verifier for Theorem A4 (General 5-Parameter Weighted Quartic-Weyl SOS):
      Let s >= 0, p > 0, gamma1 >= 0, gamma3 >= 0, kappa > 0 be rationals.
      Define:
        beta    = s + gamma3 / p
        alpha   = 1 - (beta^2 - s^2 + kappa) / (2 p)
        lambda0 = (s + gamma1 - alpha * beta) / kappa
        M       = alpha^2 + kappa * lambda0^2.

      Exact rational SOS identity verified coefficient-by-coefficient:
        M - [phi_{s,p}(lam) + 2 gamma1 lam + 2 gamma3 lam^3]
          == (p lam^2 - beta lam + alpha)^2 + kappa * (lam - lambda0)^2 >= 0   for all lam in R.
      Since phi_{s,p}(lam) <= 1_{(0, inf)}(lam) and g(lam) = 2 gamma1 lam + 2 gamma3 lam^3
      is non-decreasing on R with g(lam) <= 0 on (-inf, 0]:
        n_+(Pi_{W^perp} H Pi_{W^perp})
          >= 2s S1 - (s^2 + 2p) S2 + 2sp S3 - p^2 S4 + 2 gamma1 tr(Q) + 2 gamma3 tr(Q^3) - b * M.
    """
    b_i = parse_strict_int(b, min_value=0)
    s_f = parse_strict_fraction(s)
    p_f = parse_strict_fraction(p)
    g1_f = parse_strict_fraction(gamma1)
    g3_f = parse_strict_fraction(gamma3)
    kap_f = parse_strict_fraction(kappa)
    t1_f = parse_strict_fraction(t1_Q)
    t3_f = parse_strict_fraction(t3_Q)

    require_cert(s_f >= 0, "A4_NEGATIVE_S", "requires s >= 0")
    require_cert(p_f > 0, "A4_NONPOS_P", "requires p > 0")
    require_cert(g1_f >= 0, "A4_NEGATIVE_GAMMA1", "requires gamma1 >= 0")
    require_cert(g3_f >= 0, "A4_NEGATIVE_GAMMA3", "requires gamma3 >= 0")
    require_cert(kap_f > 0, "A4_NONPOS_KAPPA", "requires kappa > 0")
    for k in range(1, 5):
        require_cert(k in moments_H, "MISSING_SPECTRAL_MOMENT", f"S_{k} required for Theorem A4")
        parse_strict_fraction(moments_H[k])

    beta = s_f + g3_f / p_f
    alpha = Fraction(1) - (beta * beta - s_f * s_f + kap_f) / (2 * p_f)
    lam0 = (s_f + g1_f - alpha * beta) / kap_f
    M = alpha * alpha + kap_f * lam0 * lam0

    # Explicitly check exact polynomial coefficient identity:
    # (p lam^2 - beta lam + alpha)^2 + kappa (lam - lam0)^2
    # == p^2 lam^4 - 2 p beta lam^3 + (beta^2 + 2 p alpha + kappa) lam^2 - 2(alpha beta + kappa lam0) lam + M
    sos_c4 = p_f * p_f
    sos_c3 = -2 * p_f * beta
    sos_c2 = beta * beta + 2 * p_f * alpha + kap_f
    sos_c1 = -2 * (alpha * beta + kap_f * lam0)
    sos_c0 = M

    # Target M - (2(s+g1) lam - (s^2+2p) lam^2 + 2(sp+g3) lam^3 - p^2 lam^4):
    tgt_c4 = p_f * p_f
    tgt_c3 = -2 * (s_f * p_f + g3_f)
    tgt_c2 = s_f * s_f + 2 * p_f
    tgt_c1 = -2 * (s_f + g1_f)
    tgt_c0 = M
    require_cert(
        (sos_c4, sos_c3, sos_c2, sos_c1, sos_c0) == (tgt_c4, tgt_c3, tgt_c2, tgt_c1, tgt_c0),
        "A4_SOS_IDENTITY_FAIL",
        "exact polynomial SOS identity failed",
    )

    tr_phi = (
        2 * s_f * moments_H[1]
        - (s_f * s_f + 2 * p_f) * moments_H[2]
        + 2 * s_f * p_f * moments_H[3]
        - (p_f * p_f) * moments_H[4]
    )
    raw = tr_phi + 2 * g1_f * t1_f + 2 * g3_f * t3_f - Fraction(b_i) * M
    bound = raw if raw > 0 else Fraction(0)
    return {
        "theorem": "A4_Weighted_Quartic_Weyl_SOS",
        "b": b_i,
        "witness": {
            "s": frac_to_str(s_f),
            "p": frac_to_str(p_f),
            "gamma1": frac_to_str(g1_f),
            "gamma3": frac_to_str(g3_f),
            "kappa": frac_to_str(kap_f),
        },
        "M": frac_to_str(M),
        "sos_verified": True,
        "exact_bound": bound,
        "exact_bound_str": frac_to_str(bound),
    }


def certify_weighted_quartic_weyl_peak(
    moments_H: dict[int, Fraction],
    t1_Q: Any,
    b: int,
    *,
    s: Any,
    p: Any,
    mu: Any,
) -> dict[str, Any]:
    """
    Closed-form 3-parameter peak-matched specialization of Theorem A4 (gamma3 = 0, uses ONLY tr(Q)):
      Given s >= 0, p > 0, and mu > s/(2p) with q(mu) = 1 - s*mu + p*mu^2 > 0:
        gamma1 = q(mu) * (2 p mu - s) > 0
        kappa  = 2 p q(mu) > 0
      Then M - (phi_{s,p}(lam) + 2 gamma1 lam) vanishes to SECOND order at lam = mu,
      achieving exact zero slack simultaneously at lam = mu AND at the two roots of q(lam) = 0!
    """
    s_f = parse_strict_fraction(s)
    p_f = parse_strict_fraction(p)
    mu_f = parse_strict_fraction(mu)
    require_cert(s_f >= 0, "A4_NEGATIVE_S", "requires s >= 0")
    require_cert(p_f > 0, "A4_NONPOS_P", "requires p > 0")
    q_mu = Fraction(1) - s_f * mu_f + p_f * mu_f * mu_f
    qp_mu = 2 * p_f * mu_f - s_f
    require_cert(q_mu > 0, "A4_PEAK_Q_NONPOS", "peak specialization requires q(mu) > 0")
    require_cert(qp_mu >= 0, "A4_PEAK_QP_NEG", "peak specialization requires 2*p*mu - s >= 0")
    gamma1 = q_mu * qp_mu
    kappa = 2 * p_f * q_mu
    return certify_weighted_quartic_weyl(
        moments_H,
        t1_Q,
        Fraction(0),
        b,
        s=s_f,
        p=p_f,
        gamma1=gamma1,
        gamma3=Fraction(0),
        kappa=kappa,
    )


def find_weighted_quartic_witness(
    moments_H: dict[int, Fraction],
    t1_Q: Fraction,
    t3_Q: Fraction,
    b: int,
    *,
    peak_hints: Sequence[tuple[Fraction, Fraction, Fraction]] | None = None,
) -> dict[str, Any]:
    """
    Untrusted witness proposer for Theorem A4: tries exact peak hints and small-gamma1
    perturbations around the optimal Hankel-4 (s*, p*), certifying every candidate via TCB!
    """
    b_i = parse_strict_int(b, min_value=0)
    h4 = R_hankel4_exact(moments_H[1], moments_H[2], moments_H[3], moments_H[4], b_i)
    best_cert: dict[str, Any] = h4

    # 1. Try explicit (s, p, mu) peak hints (e.g. from approximate spectrum of H)
    if peak_hints:
        for s_h, p_h, mu_h in peak_hints:
            s_f = parse_strict_fraction(s_h)
            p_f = parse_strict_fraction(p_h)
            mu_f = parse_strict_fraction(mu_h)
            if s_f >= 0 and p_f > 0 and (1 - s_f * mu_f + p_f * mu_f * mu_f) > 0 and (2 * p_f * mu_f - s_f) >= 0:
                cert = certify_weighted_quartic_weyl_peak(moments_H, t1_Q, b_i, s=s_f, p=p_f, mu=mu_f)
                if cert["exact_bound"] > best_cert["exact_bound"]:
                    best_cert = cert

            # Also try attenuated gamma1 values at optimal kappa for non-commuting Q
            if s_f >= 0 and p_f > 0 and b_i > 0:
                q_mu = 1 - s_f * mu_f + p_f * mu_f * mu_f
                qp_mu = 2 * p_f * mu_f - s_f
                if q_mu > 0 and qp_mu > 0:
                    g1_peak = q_mu * qp_mu
                    for frac_g in (Fraction(1, 20), Fraction(1, 5), Fraction(1, 2), Fraction(1)):
                        g1_try = g1_peak * frac_g
                        # Optimize M(kappa) = (1 - u)^2 + (g1 + s u)^2 / (2 p u), u = kappa/(2p)
                        # Approximate optimum u* around sqrt(g1^2 / (2p + s^2))
                        denom_u = float(2 * p_f + s_f * s_f)
                        u_est = math.sqrt(float(g1_try * g1_try) / max(denom_u, 1e-12)) if g1_try > 0 else 1e-3
                        u_q = Fraction(max(u_est, 1e-4)).limit_denominator(1000)
                        kap_try = 2 * p_f * u_q
                        if kap_try > 0:
                            cert = certify_weighted_quartic_weyl(
                                moments_H, t1_Q, t3_Q, b_i,
                                s=s_f, p=p_f, gamma1=g1_try, gamma3=Fraction(0), kappa=kap_try
                            )
                            if cert["exact_bound"] > best_cert["exact_bound"]:
                                best_cert = cert

    # 2. Try boosting R_H4's (s*, p*) with small gamma1 > 0 when t1_Q > 0 and b > 0
    if b_i > 0 and t1_Q > 0:
        s0 = parse_strict_fraction(h4["witness_a"][0])
        p0 = parse_strict_fraction(h4["witness_a"][1])
        if s0 >= 0 and p0 > 0:
            for g1_num in (Fraction(1, 100), Fraction(1, 10), Fraction(1, 2), Fraction(1), Fraction(2)):
                for u_q in (Fraction(1, 20), Fraction(1, 5), Fraction(1, 2), Fraction(1)):
                    kap = 2 * p0 * u_q
                    cert = certify_weighted_quartic_weyl(
                        moments_H, t1_Q, t3_Q, b_i,
                        s=s0, p=p0, gamma1=g1_num, gamma3=Fraction(0), kappa=kap
                    )
                    if cert["exact_bound"] > best_cert["exact_bound"]:
                        best_cert = cert

    return best_cert


def best_higher_moment_bound(
    moments_H: dict[int, Fraction],
    u: Fraction,
    t1_Q: Fraction,
    b: int,
    *,
    t3_Q: Fraction = Fraction(0),
    tau_hint: Fraction = Fraction(0),
    peak_hints: Sequence[tuple[Fraction, Fraction, Fraction]] | None = None,
) -> dict[str, Any]:
    """
    Evaluate all four exact-rational theorem families (A1: R_opt, A2: R_H4 & R_H6,
    A3: Noise-Annihilating Quartic SOS, A4: Weighted Quartic-Weyl SOS) and return the
    exact maximum along with full per-theorem certificates.
    """
    ropt_val = R_opt(u, t1_Q, moments_H[2], b)
    c_h4 = R_hankel4_exact(moments_H[1], moments_H[2], moments_H[3], moments_H[4], b)
    c_h6 = R_hankel6_exact(moments_H, b) if (5 in moments_H and 6 in moments_H) else None
    c_a3_zero = find_noise_quartic_witness(moments_H, b, Fraction(0))
    c_a3_tau = find_noise_quartic_witness(moments_H, b, tau_hint) if tau_hint > 0 else c_a3_zero
    c_a4 = find_weighted_quartic_witness(moments_H, t1_Q, t3_Q, b, peak_hints=peak_hints)

    candidates: list[tuple[str, Fraction]] = [
        ("A1_R_opt", ropt_val),
        ("A2_Hankel4", c_h4["exact_bound"]),
        ("A3_NoiseQ4_tau0", c_a3_zero["exact_bound"]),
        ("A3_NoiseQ4_tau", c_a3_tau["exact_bound"]),
        ("A4_WeightedWeyl4", c_a4["exact_bound"]),
    ]
    if c_h6 is not None:
        candidates.append(("A2_Hankel6", c_h6["exact_bound"]))

    best_name, best_val = max(candidates, key=lambda kv: kv[1])
    return {
        "best_method": best_name,
        "best_bound": best_val,
        "best_bound_str": frac_to_str(best_val),
        "R_opt": ropt_val,
        "R_opt_str": frac_to_str(ropt_val),
        "strictly_beats_R_opt": best_val > ropt_val,
        "strictly_beats_ceil_R_opt": best_val > Fraction(math.ceil(ropt_val) if ropt_val > 0 else 0),
        "details": {
            "A1_R_opt": frac_to_str(ropt_val),
            "A2_Hankel4": c_h4,
            "A2_Hankel6": c_h6,
            "A3_NoiseQ4_tau0": c_a3_zero,
            "A3_NoiseQ4_tau": c_a3_tau,
            "A4_WeightedWeyl4": c_a4,
        },
    }
