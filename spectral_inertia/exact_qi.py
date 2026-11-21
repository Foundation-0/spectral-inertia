"""
Hardened R3-clean exact rational and Gaussian rational Q(i) arithmetic + Hermitian matrix primitives.

All validation failures raise CertError explicitly (zero bare asserts; 100% python3 -O parity).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json
import math
import random
import re
from typing import Any, Sequence

MAX_DIGIT_LEN = 4000
MAX_MATRIX_DIM = 64

# Strict ASCII canonical integer or p/q string:
# - Rejects leading/trailing whitespace, trailing newline (\Z not $), leading zeros ("01", "-0"),
#   plus signs ("+1"), decimals ("0.5"), scientific ("1e-5"), underscores ("1_000"),
#   zero/negative denominators ("1/0", "1/-2"), and non-ASCII digits ("\u0661/\u0662").
_STRICT_FRAC_RE = re.compile(
    r"\A(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z",
    re.ASCII,
)


class CertError(ValueError):
    """Explicit structured certificate / validation error (never stripped by python3 -O)."""

    def __init__(self, code: str, message: str) -> None:
        self.code = code
        self.message = message
        super().__init__(f"{code}: {message}")


def require_cert(cond: bool, code: str, message: str) -> None:
    """Explicit non-assert guard for TCB checks."""
    if not cond:
        raise CertError(code, message)


def parse_strict_int(val: Any, *, min_value: int | None = None, max_value: int | None = None) -> int:
    """Strictly parse an int (rejects bool, float, str, None, etc.)."""
    if isinstance(val, bool) or not isinstance(val, int):
        raise CertError("INVALID_INT_TYPE", f"expected int (not bool), got {type(val).__name__}")
    if min_value is not None and val < min_value:
        raise CertError("INT_OUT_OF_RANGE", f"integer {val} < min {min_value}")
    if max_value is not None and val > max_value:
        raise CertError("INT_OUT_OF_RANGE", f"integer {val} > max {max_value}")
    return val


def parse_strict_fraction(val: Any, *, allow_int: bool = True, allow_fraction: bool = True) -> Fraction:
    """
    R3-clean strict rational parser.
    Accepts:
      - Fraction (if allow_fraction)
      - exact int, NOT bool (if allow_int)
      - ASCII string matching \\A(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\\Z with digit guard.
    Rejects bool, float, whitespace, trailing newline, decimals, underscores, Unicode digits, "-0", etc.
    """
    if isinstance(val, bool):
        raise CertError("REJECT_BOOL_INPUT", "bool is not a valid rational")
    if isinstance(val, float):
        raise CertError("REJECT_FLOAT_INPUT", "float is forbidden in exact TCB")
    if allow_fraction and isinstance(val, Fraction):
        return val
    if allow_int and isinstance(val, int):
        return Fraction(val)
    if not isinstance(val, str):
        raise CertError("INVALID_RATIONAL_TYPE", f"unsupported rational type {type(val).__name__}")
    if len(val) == 0 or len(val) > 2 * MAX_DIGIT_LEN + 2:
        raise CertError("INVALID_RATIONAL_LENGTH", "empty or oversized rational string")
    if _STRICT_FRAC_RE.match(val) is None:
        raise CertError("INVALID_RATIONAL_SYNTAX", f"non-canonical rational string: {val!r}")
    if "/" in val:
        num_s, den_s = val.split("/")
        if len(num_s.lstrip("-")) > MAX_DIGIT_LEN or len(den_s) > MAX_DIGIT_LEN:
            raise CertError("OVERSIZED_RATIONAL_DIGITS", "digit limit exceeded")
        num_i = int(num_s)
        den_i = int(den_s)
        if den_i == 1 or math.gcd(abs(num_i), den_i) != 1:
            raise CertError("NON_CANONICAL_RATIONAL", f"rational string not in lowest terms: {val!r}")
        return Fraction(num_i, den_i)
    if len(val.lstrip("-")) > MAX_DIGIT_LEN:
        raise CertError("OVERSIZED_RATIONAL_DIGITS", "digit limit exceeded")
    return Fraction(int(val), 1)


@dataclass(frozen=True)
class Qi:
    """Exact Gaussian rational a + b*i with a, b in Q."""

    re: Fraction
    im: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        if not isinstance(self.re, Fraction) or not isinstance(self.im, Fraction):
            raise CertError("INVALID_QI_COMPONENT", "Qi components must be exact Fractions")

    def __add__(self, o: Any) -> Qi:
        if not isinstance(o, Qi):
            return NotImplemented
        return Qi(self.re + o.re, self.im + o.im)

    def __sub__(self, o: Any) -> Qi:
        if not isinstance(o, Qi):
            return NotImplemented
        return Qi(self.re - o.re, self.im - o.im)

    def __neg__(self) -> Qi:
        return Qi(-self.re, -self.im)

    def __mul__(self, o: Any) -> Qi:
        if not isinstance(o, Qi):
            return NotImplemented
        return Qi(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def conj(self) -> Qi:
        return Qi(self.re, -self.im)

    def norm_sq(self) -> Fraction:
        return self.re * self.re + self.im * self.im

    def __truediv__(self, o: Any) -> Qi:
        if not isinstance(o, Qi):
            return NotImplemented
        d = o.norm_sq()
        if d == 0:
            raise CertError("QI_DIVISION_BY_ZERO", "division by zero in Q(i)")
        c = o.conj()
        num = self * c
        return Qi(num.re / d, num.im / d)

    def is_zero(self) -> bool:
        return self.re == 0 and self.im == 0

    def is_real(self) -> bool:
        return self.im == 0

    def to_json(self) -> str | list[str]:
        if self.im == 0:
            return frac_to_str(self.re)
        return [frac_to_str(self.re), frac_to_str(self.im)]


ZERO = Qi(Fraction(0), Fraction(0))
ONE = Qi(Fraction(1), Fraction(0))
CMat = list[list[Qi]]


def frac_to_str(f: Fraction) -> str:
    if f.denominator == 1:
        return str(f.numerator)
    return f"{f.numerator}/{f.denominator}"


def parse_strict_qi(val: Any, *, allow_int: bool = True, allow_fraction: bool = True) -> Qi:
    """
    Parse a strict Gaussian rational:
      - Qi instance (if allow_fraction)
      - Real rational (str / int / Fraction)
      - 2-element list/tuple [re, im] of strict rationals.
    """
    if allow_fraction and isinstance(val, Qi):
        return val
    if isinstance(val, (list, tuple)):
        if len(val) != 2:
            raise CertError("INVALID_QI_PAIR", f"complex entry must have length 2, got {len(val)}")
        re = parse_strict_fraction(val[0], allow_int=allow_int, allow_fraction=allow_fraction)
        im = parse_strict_fraction(val[1], allow_int=allow_int, allow_fraction=allow_fraction)
        return Qi(re, im)
    re = parse_strict_fraction(val, allow_int=allow_int, allow_fraction=allow_fraction)
    return Qi(re, Fraction(0))


def parse_strict_json(raw_text: str) -> dict[str, Any]:
    """
    R1/R3-clean strict JSON object parser:
      - Rejects empty/non-str text
      - Rejects duplicate keys anywhere in the JSON tree
      - Rejects any JSON float literal
      - Rejects NaN, Infinity, -Infinity
      - Requires top-level JSON object (dict).
    """
    if not isinstance(raw_text, str) or len(raw_text.strip()) == 0:
        raise CertError("EMPTY_JSON_INPUT", "JSON input must be a non-empty string")

    def reject_float(s: str) -> Any:
        raise CertError("JSON_FLOAT_FORBIDDEN", f"float literal forbidden in JSON: {s!r}")

    def reject_constant(s: str) -> Any:
        raise CertError("JSON_CONSTANT_FORBIDDEN", f"JSON constant forbidden: {s!r}")

    def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for k, v in pairs:
            if k in out:
                raise CertError("JSON_DUPLICATE_KEY", f"duplicate JSON key: {k!r}")
            out[k] = v
        return out

    try:
        obj = json.loads(
            raw_text,
            parse_float=reject_float,
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicate_keys,
        )
    except CertError:
        raise
    except Exception as exc:
        raise CertError("JSON_SYNTAX_ERROR", str(exc)) from exc

    if not isinstance(obj, dict):
        raise CertError("JSON_ROOT_NOT_OBJECT", "top-level JSON payload must be an object")
    return obj


def parse_matrix_qi(
    rows: Any,
    *,
    max_dim: int = MAX_MATRIX_DIM,
    allow_int: bool = True,
    allow_fraction: bool = True,
    require_square: bool = True,
) -> CMat:
    """Strictly parse a non-empty matrix over Q(i) with explicit dimension guards."""
    if not isinstance(rows, (list, tuple)) or len(rows) == 0:
        raise CertError("EMPTY_MATRIX", "matrix must be a non-empty list of rows")
    n_rows = len(rows)
    if n_rows > max_dim:
        raise CertError("MATRIX_DIM_EXCEEDED", f"row count {n_rows} exceeds max_dim={max_dim}")
    if not isinstance(rows[0], (list, tuple)) or len(rows[0]) == 0:
        raise CertError("EMPTY_MATRIX_ROW", "matrix rows must be non-empty lists")
    n_cols = len(rows[0])
    if n_cols > max_dim:
        raise CertError("MATRIX_DIM_EXCEEDED", f"col count {n_cols} exceeds max_dim={max_dim}")
    if require_square and n_rows != n_cols:
        raise CertError("MATRIX_NOT_SQUARE", f"expected square matrix, got {n_rows}x{n_cols}")
    mat: CMat = []
    for r_idx, row in enumerate(rows):
        if not isinstance(row, (list, tuple)) or len(row) != n_cols:
            raise CertError("MATRIX_RAGGED", f"row {r_idx} has mismatched length")
        mat.append(
            [parse_strict_qi(v, allow_int=allow_int, allow_fraction=allow_fraction) for v in row]
        )
    return mat


def is_hermitian(A: CMat) -> bool:
    """Return True iff A is non-empty square and A[i][j] == conj(A[j][i]) with real diagonal."""
    if not isinstance(A, list) or len(A) == 0:
        return False
    n = len(A)
    for row in A:
        if not isinstance(row, list) or len(row) != n:
            return False
    for i in range(n):
        if A[i][i].im != 0:
            return False
        for j in range(i + 1, n):
            if A[i][j] != A[j][i].conj():
                return False
    return True


def parse_hermitian_matrix(
    rows: Any,
    *,
    max_dim: int = MAX_MATRIX_DIM,
    allow_int: bool = True,
    allow_fraction: bool = True,
) -> CMat:
    mat = parse_matrix_qi(
        rows,
        max_dim=max_dim,
        allow_int=allow_int,
        allow_fraction=allow_fraction,
        require_square=True,
    )
    require_cert(is_hermitian(mat), "MATRIX_NOT_HERMITIAN", "matrix is not Hermitian")
    return mat


def cmat_zeros(n: int, m: int) -> CMat:
    return [[ZERO for _ in range(m)] for _ in range(n)]


def cmat_eye(n: int) -> CMat:
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def cmat_shape(A: CMat) -> tuple[int, int]:
    require_cert(isinstance(A, list) and len(A) > 0, "EMPTY_MATRIX", "empty matrix")
    n = len(A)
    m = len(A[0])
    require_cert(m > 0 and all(len(r) == m for r in A), "MATRIX_RAGGED", "ragged matrix")
    return n, m


def cmat_add(A: CMat, B: CMat) -> CMat:
    na, ma = cmat_shape(A)
    nb, mb = cmat_shape(B)
    require_cert(na == nb and ma == mb, "DIM_MISMATCH", f"add {na}x{ma} vs {nb}x{mb}")
    return [[A[i][j] + B[i][j] for j in range(ma)] for i in range(na)]


def cmat_sub(A: CMat, B: CMat) -> CMat:
    na, ma = cmat_shape(A)
    nb, mb = cmat_shape(B)
    require_cert(na == nb and ma == mb, "DIM_MISMATCH", f"sub {na}x{ma} vs {nb}x{mb}")
    return [[A[i][j] - B[i][j] for j in range(ma)] for i in range(na)]


def cmat_scale(s: Fraction | Qi, A: CMat) -> CMat:
    sq = s if isinstance(s, Qi) else Qi(s)
    na, ma = cmat_shape(A)
    return [[sq * A[i][j] for j in range(ma)] for i in range(na)]


def cmat_dagger(A: CMat) -> CMat:
    na, ma = cmat_shape(A)
    return [[A[i][j].conj() for i in range(na)] for j in range(ma)]


def cmat_mul(A: CMat, B: CMat) -> CMat:
    na, ma = cmat_shape(A)
    nb, mb = cmat_shape(B)
    require_cert(ma == nb, "DIM_MISMATCH", f"mul {na}x{ma} by {nb}x{mb}")
    out = cmat_zeros(na, mb)
    for i in range(na):
        row_a = A[i]
        out_i = out[i]
        for k in range(ma):
            aik = row_a[k]
            if aik.is_zero():
                continue
            row_b = B[k]
            for j in range(mb):
                bkj = row_b[j]
                if not bkj.is_zero():
                    out_i[j] = out_i[j] + aik * bkj
    return out


def cmat_trace(A: CMat) -> Qi:
    n, m = cmat_shape(A)
    require_cert(n == m, "MATRIX_NOT_SQUARE", "trace requires square matrix")
    s = ZERO
    for i in range(n):
        s = s + A[i][i]
    return s


def cmat_trace_real(A: CMat) -> Fraction:
    tr = cmat_trace(A)
    require_cert(tr.im == 0, "NONREAL_TRACE", "expected real trace")
    return tr.re


def cmat_frob_sq(A: CMat) -> Fraction:
    cmat_shape(A)
    return sum((v.norm_sq() for row in A for v in row), Fraction(0))


def cmat_inv(A: CMat) -> CMat:
    """Exact Gauss-Jordan inverse over Q(i)."""
    n, m = cmat_shape(A)
    require_cert(n == m, "MATRIX_NOT_SQUARE", "inverse requires square matrix")
    I = cmat_eye(n)
    M = [A[i][:] + I[i] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if not M[r][col].is_zero():
                piv = r
                break
        require_cert(piv is not None, "MATRIX_SINGULAR", "matrix is singular")
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and not M[r][col].is_zero():
                f = M[r][col]
                M[r] = [M[r][c] - f * M[col][c] for c in range(2 * n)]
    return [row[n:] for row in M]


def cmat_rank(A: CMat) -> int:
    """Exact rank over Q(i) via Gaussian elimination."""
    n, m = cmat_shape(A)
    M = [row[:] for row in A]
    r = 0
    for col in range(m):
        piv = None
        for i in range(r, n):
            if not M[i][col].is_zero():
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            M[r], M[piv] = M[piv], M[r]
        pv = M[r][col]
        for i in range(r + 1, n):
            if not M[i][col].is_zero():
                f = M[i][col] / pv
                for j in range(col, m):
                    M[i][j] = M[i][j] - f * M[r][j]
        r += 1
    return r


def cayley_unitary(n: int, rng: random.Random, *, bound: int = 2) -> CMat:
    """Generate an exact Q(i) unitary U = (I - K)(I + K)^{-1} where K* = -K."""
    K = cmat_zeros(n, n)
    for i in range(n):
        K[i][i] = Qi(Fraction(0), Fraction(rng.randint(-bound, bound), rng.randint(1, 2)))
        for j in range(i + 1, n):
            re = Fraction(rng.randint(-bound, bound), rng.randint(1, 2))
            im = Fraction(rng.randint(-bound, bound), rng.randint(1, 2))
            K[i][j] = Qi(re, im)
            K[j][i] = Qi(-re, im)
    I = cmat_eye(n)
    return cmat_mul(cmat_sub(I, K), cmat_inv(cmat_add(I, K)))


def matrix_to_json(A: CMat) -> list[list[str | list[str]]]:
    return [[v.to_json() for v in row] for row in A]
