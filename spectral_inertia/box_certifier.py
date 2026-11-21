"""
Track B (SEAM-04): Exact Non-Affine Parametric Complex-Hermitian Inertia Box Certifier.

Zero floats in any certification path (pure fractions.Fraction + integer math.isqrt).
Zero bare asserts (100% python3 -O -B and -W error clean).

Core mathematical theorems certified:
  - Theorem B1 (Exact Multivariate Bernstein Convex-Hull Enclosure):
      For any multivariate polynomial f in Q[x_0, ..., x_{d-1}] on box B = prod [a_k, b_k],
      min(B_coeff(f, B)) <= f(x) <= max(B_coeff(f, B)) for ALL real x in B.
  - Theorem B2 (Complex Hermitian Congruent Block-Gershgorin Uniform Inertia Theorem):
      Let x_c in B be rational with exact Bunch-Kaufman congruence C M(x_c) C* = D
      (1x1 and 2x2 Hermitian blocks, nonsingular: n_0(D) = 0). Let Delta(B) be an exact
      complex rational interval enclosure of E(x) = C (M(x) - M(x_c)) C* over x in B.
      If for every block k of D:
          sigma_min_lo(D_k) > sum_{j} frob_hi(Delta_{kj}(B)),
      then D + E(x) is nonsingular for ALL real x in B. By eigenvalue continuity on the
      connected box B and Sylvester's Law of Inertia, M(x) has IDENTICAL constant inertia
      (n_+, n_-, 0) = inertia(D) at EVERY uncountably-many real point x in B!

API supports:
  1. PolyMatrix (exact Q(i)[x_0..x_{d-1}] polynomial Hermitian matrices with exact
     congruence-preconditioned Bernstein residual E(x) = C(M(x)-M(x_c))C* -> zero wrapping error!)
  2. RatMatrix (exact entrywise rational P_ij(x)/Q_ij(x) Hermitian matrices with Bernstein enclosures)
  3. General callable (eval_point(pt) -> CMat, eval_box(box) -> IntervalCMat) for piecewise
     or algebraic families (e.g. fibral-rigidity#5 two-bar truss!).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
import math
from typing import Any, Callable, Sequence

from .dual_oracle import (
    oracle_faddeev_descartes_sturm,
    produce_c_certificate,
    verify_congruence_c_cert,
)
from .exact_qi import (
    CMat,
    CertError,
    ONE,
    Qi,
    ZERO,
    cmat_dagger,
    cmat_mul,
    cmat_sub,
    frac_to_str,
    is_hermitian,
    parse_strict_fraction,
    parse_strict_int,
    require_cert,
)


# ==============================================================================
# 1. EXACT RATIONAL & GAUSSIAN-RATIONAL INTERVAL ARITHMETIC (ZERO FLOATS!)
# ==============================================================================
def exact_sqrt_bounds(q: Fraction, prec_bits: int = 40) -> tuple[Fraction, Fraction]:
    """
    Exact rational [lo, hi] bracketing sqrt(q) for q >= 0 using integer math.isqrt.
    Provably satisfies lo >= 0 and lo^2 <= q <= hi^2 with zero floating-point operations.
    """
    q_f = parse_strict_fraction(q)
    require_cert(q_f >= 0, "SQRT_NEGATIVE", f"cannot take real sqrt of negative rational {q_f}")
    if q_f == 0:
        return Fraction(0), Fraction(0)
    a, b = q_f.numerator, q_f.denominator
    S = 1 << prec_bits
    rad = a * b * S * S
    r = math.isqrt(rad)
    lo = Fraction(r, b * S)
    hi = lo if r * r == rad else Fraction(r + 1, b * S)
    require_cert(lo * lo <= q_f <= hi * hi, "SQRT_INVARIANT_FAIL", "isqrt bracket invariant violated")
    return lo, hi


@dataclass(frozen=True)
class QInterval:
    """Exact real rational interval [lo, hi] with lo <= hi."""

    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if not (isinstance(self.lo, Fraction) and isinstance(self.hi, Fraction) and self.lo <= self.hi):
            raise CertError("INVALID_QINTERVAL", f"invalid QInterval({self.lo}, {self.hi})")

    @staticmethod
    def pt(val: Fraction | int) -> QInterval:
        f = parse_strict_fraction(val)
        return QInterval(f, f)

    def mid(self) -> Fraction:
        return (self.lo + self.hi) / 2

    def width(self) -> Fraction:
        return self.hi - self.lo

    def abs_max(self) -> Fraction:
        a = -self.lo if self.lo < 0 else self.lo
        b = -self.hi if self.hi < 0 else self.hi
        return a if a >= b else b

    def contains_zero(self) -> bool:
        return self.lo <= 0 <= self.hi

    def hull(self, other: QInterval) -> QInterval:
        return QInterval(min(self.lo, other.lo), max(self.hi, other.hi))

    def __add__(self, o: QInterval | Fraction | int) -> QInterval:
        o_iv = o if isinstance(o, QInterval) else QInterval.pt(o)
        return QInterval(self.lo + o_iv.lo, self.hi + o_iv.hi)

    def __radd__(self, o: Fraction | int) -> QInterval:
        return QInterval.pt(o) + self

    def __sub__(self, o: QInterval | Fraction | int) -> QInterval:
        o_iv = o if isinstance(o, QInterval) else QInterval.pt(o)
        return QInterval(self.lo - o_iv.hi, self.hi - o_iv.lo)

    def __rsub__(self, o: Fraction | int) -> QInterval:
        return QInterval.pt(o) - self

    def __neg__(self) -> QInterval:
        return QInterval(-self.hi, -self.lo)

    def __mul__(self, o: QInterval | Fraction | int) -> QInterval:
        o_iv = o if isinstance(o, QInterval) else QInterval.pt(o)
        ps = (self.lo * o_iv.lo, self.lo * o_iv.hi, self.hi * o_iv.lo, self.hi * o_iv.hi)
        return QInterval(min(ps), max(ps))

    def __rmul__(self, o: Fraction | int) -> QInterval:
        return QInterval.pt(o) * self

    def sqr(self) -> QInterval:
        if self.lo <= 0 <= self.hi:
            return QInterval(Fraction(0), max(self.lo * self.lo, self.hi * self.hi))
        a, b = self.lo * self.lo, self.hi * self.hi
        return QInterval(min(a, b), max(a, b))

    def pow_int(self, exp: int) -> QInterval:
        e = parse_strict_int(exp, min_value=0)
        if e == 0:
            return QInterval.pt(1)
        if e == 1:
            return self
        if e == 2:
            return self.sqr()
        if e % 2 == 0:
            if self.lo <= 0 <= self.hi:
                return QInterval(Fraction(0), max(self.lo ** e, self.hi ** e))
            a, b = self.lo ** e, self.hi ** e
            return QInterval(min(a, b), max(a, b))
        return QInterval(self.lo ** e, self.hi ** e)

    def inv(self) -> QInterval:
        require_cert(not self.contains_zero(), "INTERVAL_DIV_ZERO", f"cannot invert interval containing 0: {self}")
        return QInterval(Fraction(1) / self.hi, Fraction(1) / self.lo)

    def __truediv__(self, o: QInterval | Fraction | int) -> QInterval:
        o_iv = o if isinstance(o, QInterval) else QInterval.pt(o)
        return self * o_iv.inv()

    def sqrt(self, prec_bits: int = 40) -> QInterval:
        require_cert(self.lo >= 0, "INTERVAL_SQRT_NEG", f"sqrt of interval with lo < 0: {self}")
        lo_s, _ = exact_sqrt_bounds(self.lo, prec_bits=prec_bits)
        _, hi_s = exact_sqrt_bounds(self.hi, prec_bits=prec_bits)
        return QInterval(lo_s, hi_s)


@dataclass(frozen=True)
class QiInterval:
    """Exact complex rational box [re.lo, re.hi] + i * [im.lo, im.hi]."""

    re: QInterval
    im: QInterval = field(default_factory=lambda: QInterval.pt(0))

    @staticmethod
    def pt(val: Qi | Fraction | int) -> QiInterval:
        if isinstance(val, Qi):
            return QiInterval(QInterval.pt(val.re), QInterval.pt(val.im))
        f = parse_strict_fraction(val)
        return QiInterval(QInterval.pt(f), QInterval.pt(0))

    def conj(self) -> QiInterval:
        return QiInterval(self.re, -self.im)

    def hull(self, other: QiInterval) -> QiInterval:
        return QiInterval(self.re.hull(other.re), self.im.hull(other.im))

    def __add__(self, o: QiInterval | Qi) -> QiInterval:
        o_iv = o if isinstance(o, QiInterval) else QiInterval.pt(o)
        return QiInterval(self.re + o_iv.re, self.im + o_iv.im)

    def __sub__(self, o: QiInterval | Qi) -> QiInterval:
        o_iv = o if isinstance(o, QiInterval) else QiInterval.pt(o)
        return QiInterval(self.re - o_iv.re, self.im - o_iv.im)

    def __neg__(self) -> QiInterval:
        return QiInterval(-self.re, -self.im)

    def __mul__(self, o: QiInterval | Qi) -> QiInterval:
        o_iv = o if isinstance(o, QiInterval) else QiInterval.pt(o)
        return QiInterval(
            self.re * o_iv.re - self.im * o_iv.im,
            self.re * o_iv.im + self.im * o_iv.re,
        )

    def abs_sq_hi(self) -> Fraction:
        rm = self.re.abs_max()
        im = self.im.abs_max()
        return rm * rm + im * im

    def abs_hi(self, prec_bits: int = 32) -> Fraction:
        sq = self.abs_sq_hi()
        if sq == 0:
            return Fraction(0)
        _, hi = exact_sqrt_bounds(sq, prec_bits=prec_bits)
        return hi


Box = tuple[QInterval, ...]
IntervalCMat = list[list[QiInterval]]


# ==============================================================================
# 2. EXACT MULTIVARIATE POLYNOMIALS OVER Q(i) & BERNSTEIN ENCLOSURES
# ==============================================================================
def _comb_table(max_n: int) -> list[list[int]]:
    C = [[0] * (max_n + 1) for _ in range(max_n + 1)]
    for i in range(max_n + 1):
        C[i][0] = 1
        C[i][i] = 1
        for j in range(1, i):
            C[i][j] = C[i - 1][j - 1] + C[i - 1][j]
    return C


def _power_to_bernstein_1d(coeffs: list[Fraction], a: Fraction, b: Fraction) -> list[Fraction]:
    """
    Convert univariate polynomial sum_{r=0}^m coeffs[r] x^r on [a, b]
    into exact degree-m Bernstein basis coefficients b_0, ..., b_m on [0, 1].
    """
    m = len(coeffs) - 1
    if m == 0:
        return [coeffs[0]]
    w = b - a
    C = _comb_table(m)

    # Step 1: Affine shift x = a + w*u -> power basis c_tilde[s] for u^s
    c_tilde = [Fraction(0)] * (m + 1)
    a_pows = [Fraction(1)] * (m + 1)
    w_pows = [Fraction(1)] * (m + 1)
    for k in range(1, m + 1):
        a_pows[k] = a_pows[k - 1] * a
        w_pows[k] = w_pows[k - 1] * w

    for r in range(m + 1):
        cr = coeffs[r]
        if cr == 0:
            continue
        for s in range(r + 1):
            c_tilde[s] += cr * Fraction(C[r][s]) * a_pows[r - s] * w_pows[s]

    # Step 2: Power basis on [0, 1] -> Bernstein basis:
    # b_j = sum_{s=0}^j (C(j, s) / C(m, s)) * c_tilde[s]
    bern = [Fraction(0)] * (m + 1)
    for j in range(m + 1):
        acc = Fraction(0)
        for s in range(j + 1):
            if c_tilde[s] != 0:
                acc += c_tilde[s] * Fraction(C[j][s], C[m][s])
        bern[j] = acc
    return bern


def bernstein_enclosure(
    terms: dict[tuple[int, ...], Fraction],
    box: Sequence[QInterval],
) -> QInterval:
    """
    Exact multivariate Bernstein enclosure for a real polynomial
      f(x_0, ..., x_{d-1}) = sum_{alpha} c_alpha * prod_k x_k^{alpha_k}
    over box B = [a_0, b_0] x ... x [a_{d-1}, b_{d-1}].
    Returns QInterval(min_bern, max_bern) which is PROVABLY a valid outer enclosure
    of {f(x) : x in B} by the Bernstein convex-hull theorem (and converges quadratically!).
    """
    d = len(box)
    if not terms:
        return QInterval.pt(0)
    degs = [0] * d
    for alpha in terms:
        require_cert(len(alpha) == d, "POLY_DIM_MISMATCH", f"monomial dim {len(alpha)} != {d}")
        for k in range(d):
            if alpha[k] > degs[k]:
                degs[k] = alpha[k]

    # Build flat tensor of shape (degs[0]+1, ..., degs[d-1]+1)
    strides = [1] * d
    for k in range(d - 2, -1, -1):
        strides[k] = strides[k + 1] * (degs[k + 1] + 1)
    total = strides[0] * (degs[0] + 1)
    tensor = [Fraction(0)] * total
    for alpha, coef in terms.items():
        idx = sum(alpha[k] * strides[k] for k in range(d))
        tensor[idx] += coef

    # Apply exact 1D power->Bernstein transform sequentially along each axis
    for axis in range(d):
        m_k = degs[axis]
        if m_k == 0:
            continue
        stride = strides[axis]
        block = stride * (m_k + 1)
        a_k = box[axis].lo
        b_k = box[axis].hi
        new_tensor = tensor[:]
        for base in range(0, total, block):
            for offset in range(stride):
                vec = [tensor[base + j * stride + offset] for j in range(m_k + 1)]
                b_vec = _power_to_bernstein_1d(vec, a_k, b_k)
                for j in range(m_k + 1):
                    new_tensor[base + j * stride + offset] = b_vec[j]
        tensor = new_tensor

    return QInterval(min(tensor), max(tensor))


class MultiPoly:
    """Exact multivariate polynomial over Q(i) in d variables."""

    def __init__(self, n_vars: int, terms: dict[tuple[int, ...], Qi] | None = None) -> None:
        self.n_vars = parse_strict_int(n_vars, min_value=1, max_value=16)
        self.terms: dict[tuple[int, ...], Qi] = {}
        if terms:
            for exp, coef in terms.items():
                require_cert(len(exp) == self.n_vars, "POLY_DIM_MISMATCH", "exponent tuple length mismatch")
                if not coef.is_zero():
                    self.terms[tuple(exp)] = coef

    @staticmethod
    def const(n_vars: int, c: Qi | Fraction | int) -> MultiPoly:
        cq = c if isinstance(c, Qi) else Qi(parse_strict_fraction(c))
        if cq.is_zero():
            return MultiPoly(n_vars)
        return MultiPoly(n_vars, {(0,) * n_vars: cq})

    @staticmethod
    def var(n_vars: int, idx: int) -> MultiPoly:
        i = parse_strict_int(idx, min_value=0, max_value=n_vars - 1)
        exp = tuple(1 if k == i else 0 for k in range(n_vars))
        return MultiPoly(n_vars, {exp: ONE})

    def __add__(self, o: MultiPoly | Qi | Fraction | int) -> MultiPoly:
        other = o if isinstance(o, MultiPoly) else MultiPoly.const(self.n_vars, o)
        require_cert(self.n_vars == other.n_vars, "POLY_DIM_MISMATCH", "n_vars mismatch")
        out = dict(self.terms)
        for exp, c in other.terms.items():
            nv = out.get(exp, ZERO) + c
            if nv.is_zero():
                out.pop(exp, None)
            else:
                out[exp] = nv
        return MultiPoly(self.n_vars, out)

    def __radd__(self, o: Qi | Fraction | int) -> MultiPoly:
        return MultiPoly.const(self.n_vars, o) + self

    def __sub__(self, o: MultiPoly | Qi | Fraction | int) -> MultiPoly:
        other = o if isinstance(o, MultiPoly) else MultiPoly.const(self.n_vars, o)
        return self + (-other)

    def __rsub__(self, o: Qi | Fraction | int) -> MultiPoly:
        return MultiPoly.const(self.n_vars, o) - self

    def __neg__(self) -> MultiPoly:
        return MultiPoly(self.n_vars, {e: -c for e, c in self.terms.items()})

    def __mul__(self, o: MultiPoly | Qi | Fraction | int) -> MultiPoly:
        other = o if isinstance(o, MultiPoly) else MultiPoly.const(self.n_vars, o)
        require_cert(self.n_vars == other.n_vars, "POLY_DIM_MISMATCH", "n_vars mismatch")
        out: dict[tuple[int, ...], Qi] = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in other.terms.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                nv = out.get(e, ZERO) + c1 * c2
                if nv.is_zero():
                    out.pop(e, None)
                else:
                    out[e] = nv
        return MultiPoly(self.n_vars, out)

    def __rmul__(self, o: Qi | Fraction | int) -> MultiPoly:
        return MultiPoly.const(self.n_vars, o) * self

    def conj(self) -> MultiPoly:
        return MultiPoly(self.n_vars, {e: c.conj() for e, c in self.terms.items()})

    def eval_point(self, pt: Sequence[Fraction]) -> Qi:
        require_cert(len(pt) == self.n_vars, "POLY_DIM_MISMATCH", "point length mismatch")
        acc = ZERO
        for exp, c in self.terms.items():
            mon = Fraction(1)
            for val, e in zip(pt, exp):
                if e:
                    mon *= val ** e
            acc = acc + Qi(mon) * c
        return acc

    def enclosure_bernstein(self, box: Sequence[QInterval]) -> QiInterval:
        re_terms = {e: c.re for e, c in self.terms.items() if c.re != 0}
        im_terms = {e: c.im for e, c in self.terms.items() if c.im != 0}
        return QiInterval(
            bernstein_enclosure(re_terms, box),
            bernstein_enclosure(im_terms, box),
        )


@dataclass
class PolyMatrix:
    """
    Exact Hermitian polynomial matrix M(x) in Q(i)[x_0, ..., x_{d-1}]^{n x n}.
    Supports exact congruence-preconditioned Bernstein residual E(x) = C (M(x) - M(x_c)) C*!
    """

    n_vars: int
    entries: list[list[MultiPoly]]

    def __post_init__(self) -> None:
        n = len(self.entries)
        require_cert(n > 0 and all(len(r) == n for r in self.entries), "POLYMAT_NOT_SQUARE", "must be square")
        for i in range(n):
            for j in range(n):
                require_cert(self.entries[i][j].n_vars == self.n_vars, "POLYMAT_NVARS", "n_vars mismatch")

    @property
    def dim(self) -> int:
        return len(self.entries)

    def eval_point(self, pt: Sequence[Fraction]) -> CMat:
        n = self.dim
        M = [[self.entries[i][j].eval_point(pt) for j in range(n)] for i in range(n)]
        require_cert(is_hermitian(M), "POLYMAT_NOT_HERMITIAN", "evaluated matrix is not Hermitian")
        return M

    def eval_congruent_residual_bernstein(self, C: CMat, x_c: Sequence[Fraction], box: Sequence[QInterval]) -> IntervalCMat:
        """
        Form exact polynomial matrix E(x) = C (M(x) - M(x_c)) C* FIRST,
        then take exact multivariate Bernstein enclosure of every entry on box B!
        Eliminates BOTH interval dependency error AND C(... )C* matrix wrapping error!
        """
        n = self.dim
        M_c = self.eval_point(x_c)
        # DeltaM_poly[i][j] = M[i][j](x) - M_c[i][j]
        dM = [[self.entries[i][j] - M_c[i][j] for j in range(n)] for i in range(n)]
        C_dag = cmat_dagger(C)

        # T = C * dM
        T: list[list[MultiPoly]] = [[MultiPoly(self.n_vars) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for k in range(n):
                cik = C[i][k]
                if cik.is_zero():
                    continue
                for j in range(n):
                    if dM[k][j].terms:
                        T[i][j] = T[i][j] + (cik * dM[k][j])

        # E = T * C_dag
        E_iv: IntervalCMat = [[QiInterval.pt(0) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                p_ij = MultiPoly(self.n_vars)
                for k in range(n):
                    ckj = C_dag[k][j]
                    if not ckj.is_zero() and T[i][k].terms:
                        p_ij = p_ij + (T[i][k] * ckj)
                enc = p_ij.enclosure_bernstein(box)
                if i == j:
                    # Hermitian diagonal is purely real
                    E_iv[i][i] = QiInterval(enc.re, QInterval.pt(0))
                else:
                    E_iv[i][j] = enc
                    E_iv[j][i] = enc.conj()
        return E_iv


@dataclass
class RatMatrix:
    """
    Exact entrywise rational Hermitian matrix M_{ij}(x) = num[i][j](x) / den[i][j](x),
    where den[i][j](x) are real MultiPoly strictly nonzero on the box.
    Uses centered Bernstein residual M_{ij}(x) - M_{ij}(x_c) = (P(x)Q(x_c) - P(x_c)Q(x)) / (Q(x_c)Q(x)).
    """

    n_vars: int
    num: list[list[MultiPoly]]
    den: list[list[MultiPoly]]

    def __post_init__(self) -> None:
        n = len(self.num)
        require_cert(n > 0 and len(self.den) == n, "RATMAT_DIM", "num/den size mismatch")
        require_cert(all(len(r) == n for r in self.num) and all(len(r) == n for r in self.den),
                     "RATMAT_NOT_SQUARE", "must be square")

    @property
    def dim(self) -> int:
        return len(self.num)

    def eval_point(self, pt: Sequence[Fraction]) -> CMat:
        n = self.dim
        M: CMat = []
        for i in range(n):
            row: list[Qi] = []
            for j in range(n):
                q_val = self.den[i][j].eval_point(pt)
                require_cert(q_val.is_real() and not q_val.is_zero(), "RATMAT_POLE", "zero or non-real denominator")
                p_val = self.num[i][j].eval_point(pt)
                row.append(p_val / q_val)
            M.append(row)
        require_cert(is_hermitian(M), "RATMAT_NOT_HERMITIAN", "evaluated rational matrix is not Hermitian")
        return M

    def eval_residual_box(self, x_c: Sequence[Fraction], box: Sequence[QInterval]) -> IntervalCMat:
        n = self.dim
        dM: IntervalCMat = [[QiInterval.pt(0) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                p_poly = self.num[i][j]
                q_poly = self.den[i][j]
                pc = p_poly.eval_point(x_c)
                qc = q_poly.eval_point(x_c)
                require_cert(qc.is_real() and not qc.is_zero(), "RATMAT_POLE", "pole at box center")
                q_enc = q_poly.enclosure_bernstein(box).re
                require_cert(not q_enc.contains_zero(), "RATMAT_BOX_POLE", f"denominator crosses 0 on box at ({i},{j})")
                # Exact centered numerator: P(x)*Q(x_c) - P(x_c)*Q(x)
                num_res = (p_poly * qc) - (q_poly * pc)
                num_enc = num_res.enclosure_bernstein(box)
                denom_iv = QInterval.pt(qc.re) * q_enc
                inv_d = denom_iv.inv()
                val = QiInterval(num_enc.re * inv_d, num_enc.im * inv_d)
                if i == j:
                    dM[i][i] = QiInterval(val.re, QInterval.pt(0))
                else:
                    dM[i][j] = val
                    dM[j][i] = val.conj()
        return dM


# ==============================================================================
# 3. CONGRUENT BLOCK-GERSHGORIN UNIFORM INERTIA CERTIFIER (THEOREM B2)
# ==============================================================================
def _interval_congruence(C: CMat, dM: IntervalCMat) -> IntervalCMat:
    """Compute exact complex interval matrix E = C * dM * C*."""
    n = len(C)
    # T = C * dM
    T: IntervalCMat = [[QiInterval.pt(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            cik = C[i][k]
            if cik.is_zero():
                continue
            cik_iv = QiInterval.pt(cik)
            for j in range(n):
                T[i][j] = T[i][j] + cik_iv * dM[k][j]
    C_dag = cmat_dagger(C)
    E: IntervalCMat = [[QiInterval.pt(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            acc = QiInterval.pt(0)
            for k in range(n):
                ckj = C_dag[k][j]
                if not ckj.is_zero():
                    acc = acc + T[i][k] * QiInterval.pt(ckj)
            if i == j:
                E[i][i] = QiInterval(acc.re, QInterval.pt(0))
            else:
                E[i][j] = acc
                E[j][i] = acc.conj()
    return E


def _extract_blocks_of_D(D: CMat) -> list[tuple[int, int]]:
    """Return list of (start_idx, size) blocks (size in {1, 2}) of Hermitian block-diagonal D."""
    n = len(D)
    blocks: list[tuple[int, int]] = []
    i = 0
    while i < n:
        if i + 1 < n and not D[i][i + 1].is_zero():
            blocks.append((i, 2))
            i += 2
        else:
            blocks.append((i, 1))
            i += 1
    return blocks


def _block_sigma_min_lower_bound(D: CMat, start: int, size: int, prec_bits: int = 32) -> Fraction:
    """Exact rational lower bound mu_k <= sigma_min(D_k) for a 1x1 or 2x2 Hermitian block of D."""
    if size == 1:
        v = D[start][start].re
        return -v if v < 0 else v
    # 2x2 Hermitian block [[a, b], [conj(b), c]]
    a = D[start][start].re
    b = D[start][start + 1]
    c = D[start + 1][start + 1].re
    det = a * c - b.norm_sq()
    if det == 0:
        return Fraction(0)
    abs_det = -det if det < 0 else det
    tr = a + c
    abs_tr = -tr if tr < 0 else tr
    disc = (a - c) * (a - c) + 4 * b.norm_sq()
    _, sqrt_disc_hi = exact_sqrt_bounds(disc, prec_bits=prec_bits)
    denom = abs_tr + sqrt_disc_hi
    require_cert(denom > 0, "BLOCK_DENOM_ZERO", "impossible zero denominator for nonsingular 2x2 block")
    return (2 * abs_det) / denom


def _check_block_gershgorin_nonsingular(D: CMat, E_iv: IntervalCMat, prec_bits: int = 32) -> tuple[bool, Fraction]:
    """
    Theorem B2 check: verify for every block k of D that
      sigma_min_lo(D_k) > sum_{j} frob_hi(E_{kj}).
    Returns (certified_nonsingular, min_margin).
    """
    blocks = _extract_blocks_of_D(D)
    min_margin: Fraction | None = None
    for s_k, sz_k in blocks:
        mu_k = _block_sigma_min_lower_bound(D, s_k, sz_k, prec_bits=prec_bits)
        if mu_k == 0:
            return False, Fraction(0)
        rad_k = Fraction(0)
        for s_j, sz_j in blocks:
            sq_sum = Fraction(0)
            for r in range(s_k, s_k + sz_k):
                for c in range(s_j, s_j + sz_j):
                    sq_sum += E_iv[r][c].abs_sq_hi()
            if sq_sum > 0:
                _, frob_hi = exact_sqrt_bounds(sq_sum, prec_bits=prec_bits)
                rad_k += frob_hi
        margin = mu_k - rad_k
        if min_margin is None or margin < min_margin:
            min_margin = margin
    require_cert(min_margin is not None, "EMPTY_BLOCKS", "D has no blocks")
    return (min_margin > 0), min_margin


@dataclass
class BoxCertResult:
    """Structured result of exact non-affine parametric Hermitian inertia box certification."""

    status: str  # "CERTIFIED_CONSTANT_INERTIA" | "SINGULARITY_DETECTED" | "INERTIA_CHANGE_DETECTED" | "UNRESOLVED_SUBBOXES"
    certified_inertia: tuple[int, int, int] | None
    observed_inertias: list[tuple[int, int, int]]
    certified_subboxes: int
    uncertified_subboxes: int
    max_depth_reached: int
    singular_witnesses: list[dict[str, Any]]
    inertia_change_witnesses: list[dict[str, Any]]
    uncertified_box_bounds: list[list[tuple[str, str]]]
    certified_box_list: list[dict[str, Any]]

    def to_summary_dict(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "certified_inertia": list(self.certified_inertia) if self.certified_inertia else None,
            "observed_inertias": [list(x) for x in self.observed_inertias],
            "certified_subboxes": self.certified_subboxes,
            "uncertified_subboxes": self.uncertified_subboxes,
            "max_depth_reached": self.max_depth_reached,
            "singular_witnesses": self.singular_witnesses,
            "inertia_change_witnesses": self.inertia_change_witnesses,
            "uncertified_box_count": len(self.uncertified_box_bounds),
        }


def _box_midpoint(box: Box) -> tuple[Fraction, ...]:
    return tuple(iv.mid() for iv in box)


def _split_box_widest(box: Box) -> tuple[Box, Box]:
    widths = [iv.width() for iv in box]
    axis = max(range(len(box)), key=lambda i: widths[i])
    mid = box[axis].mid()
    left = tuple(QInterval(iv.lo, mid) if i == axis else iv for i, iv in enumerate(box))
    right = tuple(QInterval(mid, iv.hi) if i == axis else iv for i, iv in enumerate(box))
    return left, right


def _box_corners(box: Box) -> list[tuple[Fraction, ...]]:
    pts: list[tuple[Fraction, ...]] = [()]
    for iv in box:
        if iv.lo == iv.hi:
            pts = [p + (iv.lo,) for p in pts]
        else:
            pts = [p + (iv.lo,) for p in pts] + [p + (iv.hi,) for p in pts]
    return pts


def certify_hermitian_box(
    family: PolyMatrix | RatMatrix | Callable[..., Any],
    box: Sequence[tuple[Fraction | int | str, Fraction | int | str] | QInterval],
    *,
    eval_box_fn: Callable[[Box], IntervalCMat] | None = None,
    eval_residual_fn: Callable[[tuple[Fraction, ...], Box], IntervalCMat] | None = None,
    max_depth: int = 10,
    max_boxes: int = 256,
    verify_witnesses_dual_oracle: bool = True,
    stop_on_singularity: bool = False,
    singular_probe_fn: Callable[[Box], list[tuple[Fraction, ...]]] | None = None,
) -> BoxCertResult:
    """
    Exact non-affine branch-and-bound inertia certifier over a continuous box B = prod [a_k, b_k].

    Accepts ANY of:
      - family = PolyMatrix (uses exact congruence-preconditioned Bernstein residual!)
      - family = RatMatrix  (uses exact centered Bernstein rational residual!)
      - family = callable eval_point(pt) -> CMat together with eval_box_fn(box) -> IntervalCMat
                 (or eval_residual_fn(x_c, box) -> IntervalCMat for tighter centered residuals).

    Guarantee (exact oracle):
      - Returns status == "CERTIFIED_CONSTANT_INERTIA" ONLY when EVERY point in B is covered
        by a certified sub-box satisfying Theorem B2 with identical exact Sylvester inertia.
      - NEVER relies on corner tests alone; isolates interior singularities & inertia flips!
    """
    parsed_box_list: list[QInterval] = []
    for item in box:
        if isinstance(item, QInterval):
            parsed_box_list.append(item)
        else:
            lo = parse_strict_fraction(item[0])
            hi = parse_strict_fraction(item[1])
            parsed_box_list.append(QInterval(lo, hi))
    root_box: Box = tuple(parsed_box_list)
    require_cert(len(root_box) >= 1, "EMPTY_BOX", "box must have at least 1 dimension")
    max_d = parse_strict_int(max_depth, min_value=0, max_value=30)
    max_b = parse_strict_int(max_boxes, min_value=1, max_value=10000)

    is_poly = isinstance(family, PolyMatrix)
    is_rat = isinstance(family, RatMatrix)

    def eval_pt(pt: tuple[Fraction, ...]) -> CMat:
        if is_poly or is_rat:
            return family.eval_point(pt)  # type: ignore[union-attr]
        return family(pt)

    def get_congruent_residual(C: CMat, x_c: tuple[Fraction, ...], M_c: CMat, sub: Box) -> IntervalCMat:
        if is_poly:
            return family.eval_congruent_residual_bernstein(C, x_c, sub)  # type: ignore[union-attr]
        if is_rat:
            dM = family.eval_residual_box(x_c, sub)  # type: ignore[union-attr]
            return _interval_congruence(C, dM)
        if eval_residual_fn is not None:
            dM = eval_residual_fn(x_c, sub)
            return _interval_congruence(C, dM)
        require_cert(eval_box_fn is not None, "MISSING_EVAL_BOX", "callable family requires eval_box_fn or eval_residual_fn")
        assert_fn = eval_box_fn
        M_iv = assert_fn(sub)
        n = len(M_c)
        dM = [
            [M_iv[i][j] - QiInterval.pt(M_c[i][j]) for j in range(n)]
            for i in range(n)
        ]
        return _interval_congruence(C, dM)

    certified_list: list[dict[str, Any]] = []
    uncertified_boxes: list[Box] = []
    singular_witnesses: list[dict[str, Any]] = []
    seen_singular_pts: set[tuple[Fraction, ...]] = set()
    inertia_examples: dict[tuple[int, int, int], tuple[Fraction, ...]] = {}
    max_depth_seen = 0

    def record_point_check(pt: tuple[Fraction, ...]) -> tuple[CMat, CMat, CMat, CMat, tuple[int, int, int]]:
        M_pt = eval_pt(pt)
        C, C_inv, D, inertia = produce_c_certificate(M_pt)
        # Always verify our own congruence certificate via Track C TCB!
        in_checked = verify_congruence_c_cert(M_pt, C, C_inv, D, claim=list(inertia))
        require_cert(in_checked == inertia, "SELF_CERT_FAIL", "produced congruence certificate failed TCB check")
        if inertia[2] > 0 and pt not in seen_singular_pts:
            seen_singular_pts.add(pt)
            o2_ok = False
            if verify_witnesses_dual_oracle:
                o2 = oracle_faddeev_descartes_sturm(M_pt)
                require_cert(o2["inertia"] == inertia, "WITNESS_DUAL_MISMATCH", "dual oracle mismatch on singular witness")
                o2_ok = True
            singular_witnesses.append({
                "point": [frac_to_str(x) for x in pt],
                "inertia": list(inertia),
                "dual_oracle_verified": o2_ok,
            })
        elif inertia[2] == 0 and inertia not in inertia_examples:
            if verify_witnesses_dual_oracle:
                o2 = oracle_faddeev_descartes_sturm(M_pt)
                require_cert(o2["inertia"] == inertia, "INERTIA_DUAL_MISMATCH", "dual oracle mismatch on nonsingular witness")
            inertia_examples[inertia] = pt
        return M_pt, C, C_inv, D, inertia

    # Stack of (sub_box, depth)
    queue: list[tuple[Box, int]] = [(root_box, 0)]
    processed = 0

    while queue:
        sub, depth = queue.pop(0)
        if depth > max_depth_seen:
            max_depth_seen = depth
        processed += 1

        x_c = _box_midpoint(sub)
        M_c, C, C_inv, D, inertia_c = record_point_check(x_c)

        certified_here = False
        if inertia_c[2] == 0:
            try:
                E_iv = get_congruent_residual(C, x_c, M_c, sub)
                ok, margin = _check_block_gershgorin_nonsingular(D, E_iv)
                if ok:
                    certified_here = True
                    certified_list.append({
                        "box": [(frac_to_str(iv.lo), frac_to_str(iv.hi)) for iv in sub],
                        "center": [frac_to_str(x) for x in x_c],
                        "inertia": list(inertia_c),
                        "gershgorin_margin_gt0": frac_to_str(margin),
                    })
            except CertError as exc:
                # E.g. pole encountered on sub-box for RatMatrix -> subdivide
                if exc.code != "RATMAT_BOX_POLE":
                    raise

        if not certified_here:
            # Check optional domain singular probe (or corners on small boxes)
            if singular_probe_fn is not None:
                for probe_pt in singular_probe_fn(sub):
                    if all(iv.lo <= x <= iv.hi for x, iv in zip(probe_pt, sub)):
                        record_point_check(probe_pt)

            if stop_on_singularity and singular_witnesses:
                uncertified_boxes.append(sub)
                break

            if depth < max_d and (processed + len(queue) + 2) <= max_b and any(iv.width() > 0 for iv in sub):
                b1, b2 = _split_box_widest(sub)
                queue.append((b1, depth + 1))
                queue.append((b2, depth + 1))
            else:
                # Also check box corners before declaring uncertified (catches exact rational boundary zeros)
                if len(sub) <= 4:
                    for cpt in _box_corners(sub):
                        record_point_check(cpt)
                uncertified_boxes.append(sub)

    # Drain remaining queue if stopped early
    for rem_sub, _ in queue:
        uncertified_boxes.append(rem_sub)

    observed = sorted(set(inertia_examples.keys()) | {tuple(w["inertia"]) for w in singular_witnesses})
    inertia_change_witnesses: list[dict[str, Any]] = []
    if len(inertia_examples) >= 2:
        items = list(inertia_examples.items())
        in_a, pt_a = items[0]
        in_b, pt_b = items[1]
        inertia_change_witnesses.append({
            "point_a": [frac_to_str(x) for x in pt_a],
            "inertia_a": list(in_a),
            "point_b": [frac_to_str(x) for x in pt_b],
            "inertia_b": list(in_b),
        })

    if len(uncertified_boxes) == 0 and len(singular_witnesses) == 0 and len(inertia_examples) == 1:
        status = "CERTIFIED_CONSTANT_INERTIA"
        cert_inertia: tuple[int, int, int] | None = next(iter(inertia_examples.keys()))
    elif len(singular_witnesses) > 0:
        status = "SINGULARITY_DETECTED"
        cert_inertia = None
    elif len(inertia_change_witnesses) > 0:
        status = "INERTIA_CHANGE_DETECTED"
        cert_inertia = None
    else:
        status = "UNRESOLVED_SUBBOXES"
        cert_inertia = None

    uncert_bounds = [
        [(frac_to_str(iv.lo), frac_to_str(iv.hi)) for iv in b]
        for b in uncertified_boxes
    ]
    return BoxCertResult(
        status=status,
        certified_inertia=cert_inertia,
        observed_inertias=observed,
        certified_subboxes=len(certified_list),
        uncertified_subboxes=len(uncertified_boxes),
        max_depth_reached=max_depth_seen,
        singular_witnesses=singular_witnesses,
        inertia_change_witnesses=inertia_change_witnesses,
        uncertified_box_bounds=uncert_bounds,
        certified_box_list=certified_list,
    )
