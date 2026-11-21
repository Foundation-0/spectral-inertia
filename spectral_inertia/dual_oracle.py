"""
Track C (SEAM-08): Hardened Dual-Oracle Exact Q(i) Inertia & Rank Certifier.

Architecture:
  - Oracle 1 (Congruence Certifier):
      Supports BOTH general congruence certificates (C * C_inv == I, C * M * C* == D)
      AND loom#7 Bunch-Kaufman certificates (P * M * P* == L * D * L*).
      Every guard uses explicit raise CertError(...) (zero bare asserts; R1-R5 clean).
  - Oracle 2 (Zero-Shared-Code Independent Spectral Inertia Oracle):
      Uses pure tuple (Fraction, Fraction) arithmetic (ZERO shared matrix/Qi code with Oracle 1).
      Computes exact characteristic polynomial via Faddeev-LeVerrier, checks Cayley-Hamilton
      identity B_n + c_n I == 0, computes exact inertia via Descartes' rule of signs (exact for
      real-rooted Hermitian polynomials), AND cross-checks against an exact Sturm sequence on
      the Yun square-free factorization of p(x)!
  - Hardened Mode A / Mode B Rank Certifiers:
      Closes all 6 AUDIT-001 exploits (missing P >= 0 witness, missing Hermitian H check,
      mismatched len(H) != len(Q), non-square C / extra D entries, R3 parser leaks,
      negative/bool target_rank_gt) and pairs with R_opt + Track A higher-moment bounds.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Any, Sequence

from .exact_qi import (
    CMat,
    CertError,
    MAX_MATRIX_DIM,
    ONE,
    Qi,
    ZERO,
    cmat_add,
    cmat_dagger,
    cmat_eye,
    cmat_frob_sq,
    cmat_inv,
    cmat_mul,
    cmat_shape,
    cmat_sub,
    cmat_trace_real,
    cmat_zeros,
    frac_to_str,
    is_hermitian,
    matrix_to_json,
    parse_hermitian_matrix,
    parse_matrix_qi,
    parse_strict_fraction,
    parse_strict_int,
    parse_strict_json,
    parse_strict_qi,
    require_cert,
)
from .higher_moments import R_opt


# ==============================================================================
# ORACLE 1: EXACT RATIONAL CONGRUENCE INERTIA CERTIFIER (C M C* = D & P M P* = L D L*)
# ==============================================================================
def _check_block_diagonal_hermitian_and_inertia(D: CMat) -> tuple[int, int, int]:
    """
    Validate that D is square Hermitian block-diagonal with non-overlapping 1x1 and 2x2 blocks,
    and return its exact Sylvester inertia (n_pos, n_neg, n_zero).

    Guards explicitly isolated for R5 mutation testing:
      - GUARD_D_HERMITIAN: D must be Hermitian (real diagonal, D[i][j] == conj(D[j][i])).
      - GUARD_D_BAND: zero outside |i - j| <= 1.
      - GUARD_D_NO_OVERLAP: no two adjacent 2x2 blocks (D[i][i+1] != 0 and D[i+1][i+2] != 0).
      - GUARD_BLOCK_2X2_NEG_DET: det < 0 -> (1, 1, 0).
      - GUARD_BLOCK_2X2_POS_DET_POS_TR: det > 0, a+c > 0 -> (2, 0, 0).
      - GUARD_BLOCK_2X2_POS_DET_NEG_TR: det > 0, a+c < 0 -> (0, 2, 0).
      - GUARD_BLOCK_2X2_ZERO_DET_POS_TR: det == 0, a+c > 0 -> (1, 0, 1).
      - GUARD_BLOCK_2X2_ZERO_DET_NEG_TR: det == 0, a+c < 0 -> (0, 1, 1).
      - GUARD_BLOCK_1X1_SIGNS: d > 0 -> pos, d < 0 -> neg, d == 0 -> zero.
    """
    n, m = cmat_shape(D)
    require_cert(n == m, "D_NOT_SQUARE", "D must be square")
    require_cert(is_hermitian(D), "D_NOT_HERMITIAN", "D must be Hermitian")

    # Band check: |i - j| > 1 must be zero
    for i in range(n):
        for j in range(n):
            if abs(i - j) > 1 and not D[i][j].is_zero():
                raise CertError("D_NOT_BLOCK_TRIDIAGONAL", f"nonzero entry outside band at ({i},{j})")

    # Overlap check: cannot have both D[i][i+1] != 0 and D[i+1][i+2] != 0
    for i in range(n - 2):
        if not D[i][i + 1].is_zero() and not D[i + 1][i + 2].is_zero():
            raise CertError("D_OVERLAPPING_2X2_BLOCKS", f"overlapping 2x2 blocks at index {i}")

    n_pos = 0
    n_neg = 0
    n_zero = 0
    i = 0
    while i < n:
        if i + 1 < n and not D[i][i + 1].is_zero():
            a = D[i][i].re
            b = D[i][i + 1]
            c = D[i + 1][i + 1].re
            det = a * c - b.norm_sq()
            tr = a + c
            if det < 0:
                n_pos += 1
                n_neg += 1
            elif det > 0:
                if tr > 0:
                    n_pos += 2
                elif tr < 0:
                    n_neg += 2
                else:
                    raise CertError("D_IMPOSSIBLE_2X2_BLOCK", "det > 0 with trace == 0 impossible")
            else:
                # det == 0 and b != 0 => a*c == |b|^2 > 0 => a, c share sign => tr != 0
                if tr > 0:
                    n_pos += 1
                    n_zero += 1
                elif tr < 0:
                    n_neg += 1
                    n_zero += 1
                else:
                    raise CertError("D_IMPOSSIBLE_2X2_BLOCK", "det == 0, b != 0 with trace == 0 impossible")
            i += 2
        else:
            d = D[i][i].re
            if d > 0:
                n_pos += 1
            elif d < 0:
                n_neg += 1
            else:
                n_zero += 1
            i += 1

    require_cert(n_pos + n_neg + n_zero == n, "INERTIA_SUM_MISMATCH", "inertia counts do not sum to n")
    return (n_pos, n_neg, n_zero)


def _check_claim(computed: tuple[int, int, int], claim: Any, n: int) -> None:
    if claim is None:
        return
    if not isinstance(claim, (list, tuple)) or len(claim) != 3:
        raise CertError("INVALID_CLAIM_FORMAT", "claim must be a 3-element list [n_pos, n_neg, n_zero]")
    cp = parse_strict_int(claim[0], min_value=0, max_value=n)
    cn = parse_strict_int(claim[1], min_value=0, max_value=n)
    cz = parse_strict_int(claim[2], min_value=0, max_value=n)
    if (cp, cn, cz) != computed:
        raise CertError(
            "INERTIA_CLAIM_MISMATCH",
            f"claimed inertia {(cp, cn, cz)} != computed {computed}",
        )


def verify_congruence_c_cert(
    M_raw: Any,
    C_raw: Any,
    C_inv_raw: Any,
    D_raw: Any,
    *,
    claim: Any = None,
    max_dim: int = MAX_MATRIX_DIM,
    allow_int: bool = True,
    allow_fraction: bool = True,
) -> tuple[int, int, int]:
    """
    Verify exact Q(i) congruence certificate:
      1. M is square n x n Hermitian (1 <= n <= max_dim).
      2. C, C_inv, D are all n x n (strictly matching M's dimension; closes AUDIT-001 exploit #4!).
      3. C * C_inv == I_n and C_inv * C == I_n (invertibility witness).
      4. D is Hermitian block-diagonal with non-overlapping 1x1 and 2x2 blocks (or diagonal vector of length n).
      5. C * M * C* == D identically in exact Q(i).
      6. Optional claim == computed inertia (n_pos, n_neg, n_zero).
    """
    M = parse_hermitian_matrix(M_raw, max_dim=max_dim, allow_int=allow_int, allow_fraction=allow_fraction)
    n = len(M)
    C = parse_matrix_qi(C_raw, max_dim=max_dim, allow_int=allow_int, allow_fraction=allow_fraction)
    C_inv = parse_matrix_qi(C_inv_raw, max_dim=max_dim, allow_int=allow_int, allow_fraction=allow_fraction)
    require_cert(len(C) == n and len(C[0]) == n, "C_DIM_MISMATCH", f"C shape does not match {n}x{n}")
    require_cert(len(C_inv) == n and len(C_inv[0]) == n, "C_INV_DIM_MISMATCH", f"C_inv shape does not match {n}x{n}")

    # Accept D either as full n x n block-diagonal matrix or as length-n diagonal list of real rationals
    if isinstance(D_raw, (list, tuple)) and len(D_raw) == n and not isinstance(D_raw[0], (list, tuple)):
        diag_vals = [parse_strict_fraction(v, allow_int=allow_int, allow_fraction=allow_fraction) for v in D_raw]
        D = cmat_zeros(n, n)
        for i, dv in enumerate(diag_vals):
            D[i][i] = Qi(dv)
    elif isinstance(D_raw, (list, tuple)) and len(D_raw) != n and (len(D_raw) == 0 or not isinstance(D_raw[0], (list, tuple))):
        raise CertError("D_DIM_MISMATCH", f"diagonal D length {len(D_raw)} != {n}")
    else:
        D = parse_matrix_qi(D_raw, max_dim=max_dim, allow_int=allow_int, allow_fraction=allow_fraction)
        require_cert(len(D) == n and len(D[0]) == n, "D_DIM_MISMATCH", f"D shape does not match {n}x{n}")

    # Verify invertibility C * C_inv == I (over field Q(i), square C * C_inv == I <=> C invertible)
    I = cmat_eye(n)
    prod_r = cmat_mul(C, C_inv)
    require_cert(prod_r == I, "C_NOT_INVERTIBLE", "C * C_inv != I")

    # Validate D block structure & read inertia
    inertia = _check_block_diagonal_hermitian_and_inertia(D)

    # Verify congruence identity C * M * C* == D
    cong = cmat_mul(cmat_mul(C, M), cmat_dagger(C))
    require_cert(cong == D, "CONGRUENCE_IDENTITY_MISMATCH", "C * M * C* != D")

    _check_claim(inertia, claim, n)
    return inertia


def verify_congruence_pldl_cert(
    payload: dict[str, Any] | str,
    *,
    max_dim: int = MAX_MATRIX_DIM,
    strict_string_entries: bool = True,
) -> tuple[int, int, int]:
    """
    Verify a loom#7-compatible exact Q(i) P * M * P* = L * D * L* JSON certificate
    with zero shared code from loom#7.
    """
    if isinstance(payload, str):
        obj = parse_strict_json(payload)
    elif isinstance(payload, dict):
        obj = payload
    else:
        raise CertError("INVALID_CERT_PAYLOAD", "certificate payload must be JSON string or dict")

    allowed_keys = {"M", "P", "L", "D", "claim"}
    required_keys = {"M", "P", "L", "D"}
    keys = set(obj.keys())
    if not required_keys.issubset(keys):
        missing = sorted(required_keys - keys)
        raise CertError("MISSING_CERT_KEYS", f"missing required keys: {missing}")
    extra = sorted(keys - allowed_keys)
    if extra:
        raise CertError("UNEXPECTED_CERT_KEYS", f"unexpected keys: {extra}")

    allow_num = not strict_string_entries
    M = parse_hermitian_matrix(obj["M"], max_dim=max_dim, allow_int=allow_num, allow_fraction=allow_num)
    n = len(M)

    # Validate permutation P of 0..n-1
    P_raw = obj["P"]
    if not isinstance(P_raw, (list, tuple)) or len(P_raw) != n:
        raise CertError("INVALID_PERMUTATION_LEN", f"P must have length {n}")
    P_perm = [parse_strict_int(x, min_value=0, max_value=n - 1) for x in P_raw]
    if len(set(P_perm)) != n:
        raise CertError("INVALID_PERMUTATION_DUPLICATE", "P must be a bijection of 0..n-1")

    # Validate unit lower triangular L
    L = parse_matrix_qi(obj["L"], max_dim=max_dim, allow_int=allow_num, allow_fraction=allow_num)
    require_cert(len(L) == n and len(L[0]) == n, "L_DIM_MISMATCH", f"L shape does not match {n}x{n}")
    for i in range(n):
        if L[i][i] != ONE:
            raise CertError("L_NOT_UNIT_DIAGONAL", f"L[{i}][{i}] != 1")
        for j in range(i + 1, n):
            if not L[i][j].is_zero():
                raise CertError("L_NOT_LOWER_TRIANGULAR", f"nonzero upper entry L[{i}][{j}]")

    # Validate D block structure & read inertia
    D = parse_matrix_qi(obj["D"], max_dim=max_dim, allow_int=allow_num, allow_fraction=allow_num)
    require_cert(len(D) == n and len(D[0]) == n, "D_DIM_MISMATCH", f"D shape does not match {n}x{n}")
    inertia = _check_block_diagonal_hermitian_and_inertia(D)

    # Verify P * M * P* == L * D * L*
    PMP = [[M[P_perm[i]][P_perm[j]] for j in range(n)] for i in range(n)]
    LDL = cmat_mul(cmat_mul(L, D), cmat_dagger(L))
    require_cert(PMP == LDL, "PLDL_IDENTITY_MISMATCH", "P * M * P* != L * D * L*")

    _check_claim(inertia, obj.get("claim"), n)
    return inertia


# ==============================================================================
# UNTRUSTED BUNCH-KAUFMAN PRODUCER OVER Q(i) (PRODUCES BOTH P M P* = L D L* AND C M C* = D)
# ==============================================================================
def produce_pldl_certificate(M: CMat) -> dict[str, Any]:
    """
    Exact Q(i) Bunch-Kaufman-style symmetric/Hermitian block LDL* factorization.
    Handles arbitrary indefinite Hermitian matrices including zero diagonals via 1x1 & 2x2 pivots.
    Produces a self-contained JSON-serializable certificate dict {M, P, L, D, claim}.
    """
    require_cert(is_hermitian(M), "MATRIX_NOT_HERMITIAN", "producer requires Hermitian M")
    n = len(M)
    A = [row[:] for row in M]
    perm = list(range(n))
    L = cmat_eye(n)
    D = cmat_zeros(n, n)

    def swap_rc(idx1: int, idx2: int) -> None:
        if idx1 == idx2:
            return
        perm[idx1], perm[idx2] = perm[idx2], perm[idx1]
        A[idx1], A[idx2] = A[idx2], A[idx1]
        for row in A:
            row[idx1], row[idx2] = row[idx2], row[idx1]
        # Swap already-computed columns 0..k-1 of L
        for c in range(k):
            L[idx1][c], L[idx2][c] = L[idx2][c], L[idx1][c]

    k = 0
    while k < n:
        # 1. Look for largest |A[i][i]| among i >= k
        best_diag = None
        best_diag_val = Fraction(0)
        for i in range(k, n):
            av = abs(A[i][i].re)
            if av > best_diag_val:
                best_diag_val = av
                best_diag = i

        if best_diag is not None:
            swap_rc(k, best_diag)
            piv = A[k][k]
            D[k][k] = piv
            for i in range(k + 1, n):
                lik = A[i][k] / piv
                L[i][k] = lik
            for i in range(k + 1, n):
                lik = L[i][k]
                if lik.is_zero():
                    continue
                for j in range(k + 1, n):
                    A[i][j] = A[i][j] - lik * A[k][j]
            k += 1
            continue

        # 2. All remaining diagonal entries are zero! Find any nonzero off-diagonal (i, j) with k <= i < j < n
        found_pair = None
        for i in range(k, n):
            for j in range(i + 1, n):
                if not A[i][j].is_zero():
                    found_pair = (i, j)
                    break
            if found_pair is not None:
                break

        if found_pair is None:
            # Remaining trailing submatrix is identically zero -> 1x1 zero blocks
            break

        p_i, p_j = found_pair
        swap_rc(k, p_i)
        if p_j == k:
            p_j = p_i
        swap_rc(k + 1, p_j)

        # Now A[k][k] == 0, A[k+1][k+1] == 0, b = A[k][k+1] != 0
        b = A[k][k + 1]
        b_bar = b.conj()
        D[k][k] = ZERO
        D[k][k + 1] = b
        D[k + 1][k] = b_bar
        D[k + 1][k + 1] = ZERO

        # Inverse of [[0, b], [b_bar, 0]] is [[0, 1/b_bar], [1/b, 0]]
        # For i >= k+2: [L[i][k], L[i][k+1]] * D_2x2 = [A[i][k], A[i][k+1]]
        # => L[i][k+1] * b_bar = A[i][k]  => L[i][k+1] = A[i][k] / b_bar
        # => L[i][k]   * b     = A[i][k+1] => L[i][k]   = A[i][k+1] / b
        for i in range(k + 2, n):
            L[i][k] = A[i][k + 1] / b
            L[i][k + 1] = A[i][k] / b_bar

        # Schur complement: A_rem -= L_rem * D_2x2 * L_rem* = L_rem * [A[k][j], A[k+1][j]]^T
        for i in range(k + 2, n):
            lik0 = L[i][k]
            lik1 = L[i][k + 1]
            for j in range(k + 2, n):
                A[i][j] = A[i][j] - (lik0 * A[k][j] + lik1 * A[k + 1][j])
        k += 2

    inertia = _check_block_diagonal_hermitian_and_inertia(D)
    return {
        "M": matrix_to_json(M),
        "P": perm,
        "L": matrix_to_json(L),
        "D": matrix_to_json(D),
        "claim": [inertia[0], inertia[1], inertia[2]],
    }


def produce_c_certificate(M: CMat) -> tuple[CMat, CMat, CMat, tuple[int, int, int]]:
    """
    Produce exact Q(i) matrices (C, C_inv, D) and inertia such that C * C_inv == I and C * M * C* == D.
    """
    cert = produce_pldl_certificate(M)
    n = len(M)
    perm = cert["P"]
    L = parse_matrix_qi(cert["L"], max_dim=max(n, MAX_MATRIX_DIM))
    D = parse_matrix_qi(cert["D"], max_dim=max(n, MAX_MATRIX_DIM))
    # P M P* = L D L* => (L^-1 P) M (L^-1 P)* = D
    L_inv = cmat_inv(L)
    P_mat = cmat_zeros(n, n)
    for i, pi in enumerate(perm):
        P_mat[i][pi] = ONE
    C = cmat_mul(L_inv, P_mat)
    # C_inv = P^T L
    P_T = cmat_dagger(P_mat)
    C_inv = cmat_mul(P_T, L)
    inertia = (cert["claim"][0], cert["claim"][1], cert["claim"][2])
    return C, C_inv, D, inertia


# ==============================================================================
# ORACLE 2: ZERO-SHARED-CODE INDEPENDENT SPECTRAL INERTIA ORACLE
# (Faddeev-LeVerrier + Cayley-Hamilton Self-Check + Descartes AND Exact Sturm)
# ==============================================================================
# Note: Intentionally uses ONLY raw tuple (Fraction, Fraction) arithmetic —
# ZERO calls to Qi, cmat_mul, cmat_inv, or any Oracle 1 function!

_CTuple = tuple[Fraction, Fraction]


def _ct_add(a: _CTuple, b: _CTuple) -> _CTuple:
    return (a[0] + b[0], a[1] + b[1])


def _ct_mul(a: _CTuple, b: _CTuple) -> _CTuple:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _ct_mat_mul(A: list[list[_CTuple]], B: list[list[_CTuple]]) -> list[list[_CTuple]]:
    n = len(A)
    z = (Fraction(0), Fraction(0))
    out = [[z for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            aik = A[i][k]
            if aik[0] == 0 and aik[1] == 0:
                continue
            for j in range(n):
                bkj = B[k][j]
                if bkj[0] != 0 or bkj[1] != 0:
                    out[i][j] = _ct_add(out[i][j], _ct_mul(aik, bkj))
    return out


# Exact univariate rational polynomial helpers (descending degree: [c_d, c_{d-1}, ..., c_0])
def _poly_trim(p: list[Fraction]) -> list[Fraction]:
    idx = 0
    while idx < len(p) - 1 and p[idx] == 0:
        idx += 1
    return p[idx:]


def _poly_monic(p: list[Fraction]) -> list[Fraction]:
    p = _poly_trim(p)
    if p[0] == 0:
        return [Fraction(0)]
    lead = p[0]
    return [c / lead for c in p]


def _poly_deriv(p: list[Fraction]) -> list[Fraction]:
    deg = len(p) - 1
    if deg <= 0:
        return [Fraction(0)]
    return [p[i] * Fraction(deg - i) for i in range(deg)]


def _poly_divmod(a: list[Fraction], b: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    a = _poly_trim(a)
    b = _poly_trim(b)
    if b == [Fraction(0)]:
        raise CertError("POLY_DIV_ZERO", "polynomial division by zero")
    if len(a) < len(b):
        return [Fraction(0)], a
    rem = a[:]
    deg_b = len(b) - 1
    lead_b = b[0]
    quot = [Fraction(0)] * (len(a) - len(b) + 1)
    for i in range(len(quot)):
        coef = rem[i] / lead_b
        quot[i] = coef
        if coef != 0:
            for j in range(deg_b + 1):
                rem[i + j] -= coef * b[j]
    return _poly_trim(quot), _poly_trim(rem)


def _poly_gcd(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    a = _poly_trim(a)
    b = _poly_trim(b)
    while b != [Fraction(0)]:
        _, r = _poly_divmod(a, b)
        a, b = b, r
    return _poly_monic(a)


def _poly_sign_changes_nonzero(seq: list[Fraction]) -> int:
    nz = [x for x in seq if x != 0]
    return sum(1 for u, v in zip(nz, nz[1:]) if (u > 0) != (v > 0))


def _sturm_count_distinct_pos_neg(sqfree_p: list[Fraction]) -> tuple[int, int]:
    """
    Count exact number of distinct positive roots and distinct negative roots of a
    square-free polynomial sqfree_p(x) with sqfree_p(0) != 0 using Sturm's theorem.
    """
    p0 = _poly_monic(sqfree_p)
    deg = len(p0) - 1
    if deg == 0:
        return (0, 0)
    chain: list[list[Fraction]] = [p0, _poly_deriv(p0)]
    while len(chain[-1]) > 1:
        _, rem = _poly_divmod(chain[-2], chain[-1])
        if rem == [Fraction(0)]:
            break
        chain.append([-c for c in rem])

    def signs_at_pos_inf() -> list[Fraction]:
        return [poly[0] for poly in chain]

    def signs_at_neg_inf() -> list[Fraction]:
        return [poly[0] if ((len(poly) - 1) % 2 == 0) else -poly[0] for poly in chain]

    def signs_at_zero() -> list[Fraction]:
        return [poly[-1] for poly in chain]

    v_neg_inf = _poly_sign_changes_nonzero(signs_at_neg_inf())
    v_zero = _poly_sign_changes_nonzero(signs_at_zero())
    v_pos_inf = _poly_sign_changes_nonzero(signs_at_pos_inf())
    distinct_pos = v_zero - v_pos_inf
    distinct_neg = v_neg_inf - v_zero
    return (distinct_pos, distinct_neg)


def _sturm_exact_inertia_from_charpoly(coeffs: list[Fraction]) -> tuple[int, int, int]:
    """
    Compute exact root counts (n_pos, n_neg, n_zero) WITH MULTIPLICITIES of p(x) in Q[x]
    via exact square-free factorization (p / gcd(p, p')) + Sturm's theorem on each factor!
    """
    p = _poly_trim(coeffs[:])
    n_zero = 0
    while len(p) > 1 and p[-1] == 0:
        p.pop()
        n_zero += 1

    # Repeatedly peel off square-free product g_k = p_curr / gcd(p_curr, p_curr')
    # Each distinct root of multiplicity m appears in exactly m iterations of this peel!
    n_pos = 0
    n_neg = 0
    curr = _poly_monic(p)
    while len(curr) > 1:
        g = _poly_gcd(curr, _poly_deriv(curr))
        sqfree, rem = _poly_divmod(curr, g)
        require_cert(rem == [Fraction(0)], "STURM_SQFREE_ERROR", "exact division failed in square-free peel")
        dp, dn = _sturm_count_distinct_pos_neg(sqfree)
        n_pos += dp
        n_neg += dn
        curr = g
    return (n_pos, n_neg, n_zero)


def oracle_faddeev_descartes_sturm(M_raw: Any, *, max_dim: int = MAX_MATRIX_DIM) -> dict[str, Any]:
    """
    Zero-shared-code independent exact Q(i) Hermitian inertia oracle.
    Computes exact characteristic polynomial via Faddeev-LeVerrier, verifies Cayley-Hamilton,
    and cross-checks exact inertia via BOTH Descartes' rule of signs AND exact Sturm sequences!
    """
    # Independent parsing directly to raw (Fraction, Fraction) tuples
    if not isinstance(M_raw, (list, tuple)) or len(M_raw) == 0:
        raise CertError("ORACLE2_EMPTY_MATRIX", "matrix must be non-empty")
    n = len(M_raw)
    if n > max_dim:
        raise CertError("ORACLE2_DIM_EXCEEDED", f"n={n} > max_dim={max_dim}")

    H: list[list[_CTuple]] = []
    for i in range(n):
        row = M_raw[i]
        if not isinstance(row, (list, tuple)) or len(row) != n:
            raise CertError("ORACLE2_NOT_SQUARE", "matrix must be square")
        h_row: list[_CTuple] = []
        for j in range(n):
            v = row[j]
            if isinstance(v, Qi):
                h_row.append((v.re, v.im))
            elif isinstance(v, (list, tuple)):
                if len(v) != 2:
                    raise CertError("ORACLE2_BAD_ENTRY", "complex tuple must have len 2")
                h_row.append((parse_strict_fraction(v[0]), parse_strict_fraction(v[1])))
            else:
                h_row.append((parse_strict_fraction(v), Fraction(0)))
        H.append(h_row)

    # Independent Hermitian check
    for i in range(n):
        if H[i][i][1] != 0:
            raise CertError("ORACLE2_NOT_HERMITIAN", f"non-real diagonal at ({i},{i})")
        for j in range(i + 1, n):
            if H[i][j][0] != H[j][i][0] or H[i][j][1] != -H[j][i][1]:
                raise CertError("ORACLE2_NOT_HERMITIAN", f"Hermitian mismatch at ({i},{j})")

    # Faddeev-LeVerrier
    coeffs: list[Fraction] = [Fraction(1)]
    B = H
    tr_re = sum((B[i][i][0] for i in range(n)), Fraction(0))
    tr_im = sum((B[i][i][1] for i in range(n)), Fraction(0))
    require_cert(tr_im == 0, "ORACLE2_NONREAL_TRACE", "Faddeev trace imaginary part nonzero")
    coeffs.append(-tr_re)
    for k in range(2, n + 1):
        shifted = [row[:] for row in B]
        ck_prev = coeffs[-1]
        for i in range(n):
            shifted[i][i] = (shifted[i][i][0] + ck_prev, shifted[i][i][1])
        B = _ct_mat_mul(H, shifted)
        tr_re = sum((B[i][i][0] for i in range(n)), Fraction(0))
        tr_im = sum((B[i][i][1] for i in range(n)), Fraction(0))
        require_cert(tr_im == 0, "ORACLE2_NONREAL_TRACE", "Faddeev trace imaginary part nonzero")
        coeffs.append(-tr_re / Fraction(k))

    # Internal Cayley-Hamilton self-check: B_n + c_n I == 0
    cn = coeffs[-1]
    for i in range(n):
        for j in range(n):
            re_val = B[i][j][0] + (cn if i == j else Fraction(0))
            im_val = B[i][j][1]
            require_cert(re_val == 0 and im_val == 0, "ORACLE2_CAYLEY_HAMILTON_FAIL", "B_n + c_n I != 0")

    # Method 2A: Exact Descartes' rule of signs (exact since Hermitian => all roots real)
    d_coeffs = coeffs[:]
    d_zero = 0
    while len(d_coeffs) > 1 and d_coeffs[-1] == 0:
        d_coeffs.pop()
        d_zero += 1
    d_pos = _poly_sign_changes_nonzero(d_coeffs)
    d_alt = [c if (k % 2 == 0) else -c for k, c in enumerate(d_coeffs)]
    d_neg = _poly_sign_changes_nonzero(d_alt)
    require_cert(d_pos + d_neg + d_zero == n, "ORACLE2_DESCARTES_SUM_FAIL", "Descartes count != n")
    descartes_inertia = (d_pos, d_neg, d_zero)

    # Method 2B: Independent Exact Sturm Sequence on Square-Free Factorization
    sturm_inertia = _sturm_exact_inertia_from_charpoly(coeffs)
    require_cert(
        sturm_inertia == descartes_inertia,
        "ORACLE2_STURM_DESCARTES_DISAGREE",
        f"Sturm {sturm_inertia} != Descartes {descartes_inertia}",
    )

    return {
        "inertia": descartes_inertia,
        "descartes_inertia": descartes_inertia,
        "sturm_inertia": sturm_inertia,
        "charpoly_desc": [frac_to_str(c) for c in coeffs],
        "cayley_hamilton_verified": True,
    }


def verify_inertia_dual_oracle(
    payload: dict[str, Any] | str,
    *,
    mode: str = "pldl",
    max_dim: int = MAX_MATRIX_DIM,
    strict_string_entries: bool = True,
) -> dict[str, Any]:
    """
    Dual-Oracle Exact Inertia Certifier:
      Runs Oracle 1 (Sylvester congruence) AND Oracle 2 (zero-shared-code Faddeev-LeVerrier
      + Cayley-Hamilton + Descartes + Sturm) and requires exact agreement!
    """
    if isinstance(payload, str):
        obj = parse_strict_json(payload)
    elif isinstance(payload, dict):
        obj = payload
    else:
        raise CertError("INVALID_DUAL_PAYLOAD", "payload must be JSON string or dict")

    if mode == "pldl":
        inertia_1 = verify_congruence_pldl_cert(
            obj, max_dim=max_dim, strict_string_entries=strict_string_entries
        )
        M_raw = obj["M"]
    elif mode == "c_cert":
        required_keys = {"M", "C", "C_inv", "D"}
        allowed_keys = {"M", "C", "C_inv", "D", "claim"}
        keys = set(obj.keys())
        if not required_keys.issubset(keys):
            raise CertError("MISSING_CERT_KEYS", f"missing keys: {sorted(required_keys - keys)}")
        extra = sorted(keys - allowed_keys)
        if extra:
            raise CertError("UNEXPECTED_CERT_KEYS", f"unexpected keys: {extra}")
        allow_num = not strict_string_entries
        inertia_1 = verify_congruence_c_cert(
            obj["M"],
            obj["C"],
            obj["C_inv"],
            obj["D"],
            claim=obj.get("claim"),
            max_dim=max_dim,
            allow_int=allow_num,
            allow_fraction=allow_num,
        )
        M_raw = obj["M"]
    else:
        raise CertError("UNKNOWN_CERT_MODE", f"unsupported mode {mode!r}")

    o2 = oracle_faddeev_descartes_sturm(M_raw, max_dim=max_dim)
    inertia_2 = o2["inertia"]
    require_cert(
        inertia_1 == inertia_2,
        "DUAL_ORACLE_DISAGREEMENT",
        f"Oracle 1 {inertia_1} != Oracle 2 {inertia_2}",
    )
    return {
        "verified": True,
        "mode": mode,
        "inertia": inertia_1,
        "oracle1_congruence": inertia_1,
        "oracle2_descartes": o2["descartes_inertia"],
        "oracle2_sturm": o2["sturm_inertia"],
        "cayley_hamilton_verified": o2["cayley_hamilton_verified"],
    }


# ==============================================================================
# HARDENED MODE A & MODE B CHIMERIC / NOVEL-SUBSPACE RANK CERTIFIERS
# (Closes all 6 exploits from AUDIT-001 + upgrades to R_opt & dual-oracle checks!)
# ==============================================================================
def certify_mode_a_hardened(
    G_raw: Any,
    noise_diag_raw: Sequence[Any],
    *,
    target_rank_gt: int = 1,
    max_dim: int = MAX_MATRIX_DIM,
) -> dict[str, Any]:
    """
    Hardened sequence-agnostic b=0 rank certifier: H = G - diag(noise_diag).
    Certifies rank(P_signal) >= n_+(H) >= target_rank_gt + 1.
    """
    r0 = parse_strict_int(target_rank_gt, min_value=0)
    G = parse_hermitian_matrix(G_raw, max_dim=max_dim)
    n = len(G)
    if not isinstance(noise_diag_raw, (list, tuple)) or len(noise_diag_raw) != n:
        raise CertError("INVALID_NOISE_DIAG_LEN", f"noise_diag must have length {n}")
    noise_diag = [parse_strict_fraction(v) for v in noise_diag_raw]
    if any(t < 0 for t in noise_diag):
        raise CertError("NEGATIVE_NOISE_FLOOR", "noise_diag entries must be >= 0")

    H = [row[:] for row in G]
    for i in range(n):
        H[i][i] = H[i][i] - Qi(noise_diag[i])

    tr_h = cmat_trace_real(H)
    s_h = cmat_frob_sq(H)
    if tr_h <= 0 or s_h <= 0:
        raise CertError("RANK_BOUND_NOT_CERTIFIED", "non-positive trace or Frobenius norm of H")

    lhs = tr_h * tr_h
    rhs = Fraction(r0) * s_h
    if lhs <= rhs:
        raise CertError(
            "RANK_BOUND_NOT_CERTIFIED",
            f"exact bound {frac_to_str(lhs / s_h)} <= target_rank_gt {r0}",
        )
    bound = lhs / s_h
    return {
        "mode": "hardened_mode_a_b0",
        "certified_min_rank": r0 + 1,
        "trace_H": frac_to_str(tr_h),
        "hs_norm_sq_H": frac_to_str(s_h),
        "exact_bound": frac_to_str(bound),
    }


def certify_mode_b_hardened(
    H_raw: Any,
    Q_raw: Any,
    C_Q_raw: Any,
    C_Q_inv_raw: Any,
    D_Q_raw: Any,
    C_P_raw: Any,
    C_P_inv_raw: Any,
    D_P_raw: Any,
    *,
    target_rank_gt: int = 0,
    use_ropt: bool = True,
    c: Any = Fraction(2),
    run_dual_oracle: bool = True,
    max_dim: int = MAX_MATRIX_DIM,
) -> dict[str, Any]:
    """
    Hardened Mode B exact Q(i) rank & projected novel-subspace certifier.
    Closes EVERY SINGLE exploit from AUDIT-001:
      1. Strictly parses target_rank_gt >= 0 (rejects bool and negative ints).
      2. Verifies H is square Hermitian AND Q is square Hermitian AND len(H) == len(Q).
      3. Verifies Q congruence witness (C_Q, C_Q_inv, D_Q) with exact dimension matching -> b = n_+(Q).
      4. Computes P := H - Q and verifies P >= 0 via second congruence witness (C_P, C_P_inv, D_P)
         requiring n_neg(P) == 0 (closes the critical missing-P-PSD forgery!).
      5. Optionally cross-checks BOTH Q and P against independent Oracle 2 (Faddeev-LeVerrier +
         Descartes + Sturm).
      6. Certifies rank(P) >= rank(Pi_{W^perp} P Pi_{W^perp}) >= n_+(Pi_{W^perp} H Pi_{W^perp})
         >= target_rank_gt + 1 via guarded R_opt(u, t, S, b) or generalized Lemma 3.2 (c >= 1).
    """
    r0 = parse_strict_int(target_rank_gt, min_value=0)
    H = parse_hermitian_matrix(H_raw, max_dim=max_dim)
    Q = parse_hermitian_matrix(Q_raw, max_dim=max_dim)
    require_cert(len(H) == len(Q), "H_Q_DIM_MISMATCH", f"len(H)={len(H)} != len(Q)={len(Q)}")

    # 1. Verify Q inertia witness -> b = n_+(Q)
    q_pos, q_neg, q_zero = verify_congruence_c_cert(
        Q, C_Q_raw, C_Q_inv_raw, D_Q_raw, max_dim=max_dim
    )
    b = q_pos

    # 2. Compute P = H - Q and verify P >= 0 via second congruence witness!
    P = cmat_sub(H, Q)
    p_pos, p_neg, p_zero = verify_congruence_c_cert(
        P, C_P_raw, C_P_inv_raw, D_P_raw, max_dim=max_dim
    )
    require_cert(p_neg == 0, "P_NOT_PSD", f"P = H - Q has {p_neg} negative eigenvalues (must be 0)")

    # 3. Independent dual-oracle cross-check on both Q and P
    if run_dual_oracle:
        o2_q = oracle_faddeev_descartes_sturm(Q, max_dim=max_dim)
        require_cert(
            o2_q["inertia"] == (q_pos, q_neg, q_zero),
            "DUAL_ORACLE_Q_DISAGREEMENT",
            f"Q oracle mismatch: {o2_q['inertia']} vs {(q_pos, q_neg, q_zero)}",
        )
        o2_p = oracle_faddeev_descartes_sturm(P, max_dim=max_dim)
        require_cert(
            o2_p["inertia"] == (p_pos, p_neg, p_zero),
            "DUAL_ORACLE_P_DISAGREEMENT",
            f"P oracle mismatch: {o2_p['inertia']} vs {(p_pos, p_neg, p_zero)}",
        )

    u = cmat_trace_real(P)
    t = cmat_trace_real(Q)
    S = cmat_frob_sq(H)

    if use_ropt:
        bound = R_opt(u, t, S, b)
        method = "R_opt_projected_novel_subspace"
    else:
        c_val = parse_strict_fraction(c)
        require_cert(c_val >= 1, "INVALID_WEIGHT_C", "generalized Lemma 3.2 requires c >= 1")
        Tc = u + c_val * t
        if u <= 0 or Tc <= 0 or S <= 0:
            bound = Fraction(0)
        else:
            raw = (Tc * Tc) / S - c_val * c_val * Fraction(b)
            bound = raw if raw > 0 else Fraction(0)
        method = f"lemma32_c={frac_to_str(c_val)}"

    if bound <= Fraction(r0):
        raise CertError(
            "RANK_BOUND_NOT_CERTIFIED",
            f"exact bound {frac_to_str(bound)} <= target_rank_gt {r0}",
        )

    return {
        "mode": "hardened_mode_b",
        "method": method,
        "certified_n_plus_Q": b,
        "certified_P_is_PSD": True,
        "certified_min_projected_pos_inertia": r0 + 1,
        "certified_min_rank": r0 + 1,
        "u_tr_P": frac_to_str(u),
        "t_tr_Q": frac_to_str(t),
        "S_frob_sq_H": frac_to_str(S),
        "exact_bound": frac_to_str(bound),
        "dual_oracle_verified": run_dual_oracle,
    }
