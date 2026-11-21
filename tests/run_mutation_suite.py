#!/usr/bin/env python3
"""
Track C (R5 Gate Integrity): 36-Mutant Refusal-Site & Check-Deletion Adversarial Suite.

Inspired by siliconcordat/loom#9 (Gate Contract R5):
  Every single named refusal guard across exact_qi.py, dual_oracle.py, and higher_moments.py
  is individually sabotaged in an IN-MEMORY copy of the source code (never modifying files on disk!),
  loaded into an isolated module namespace, and tested against its minimal must-fail control.
  A mutant is KILLED iff sabotaging that single guard causes a corrupted/forged input to be
  falsely accepted (or produces a wrong mathematical verdict) that the unmutated checker REJECTS!

  Zero bare asserts (100% python3 -O -B and -B -W error clean).
  Target: 36/36 mutants KILLED, 0 survivors!
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys
import types
from typing import Any, Callable

PKG_DIR = Path(__file__).resolve().parent.parent / "spectral_inertia"


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"MUTATION SUITE ERROR: {msg}")


def load_mutated_package(file_name: str, target_snippet: str, replacement_snippet: str) -> dict[str, types.ModuleType]:
    """
    Load an isolated copy of spectral_inertia in memory with ONE single mutation applied
    to `file_name`. Verifies that `target_snippet` appears EXACTLY ONCE (no silent no-op mutations!).
    """
    src_exact = (PKG_DIR / "exact_qi.py").read_text(encoding="utf-8")
    src_dual = (PKG_DIR / "dual_oracle.py").read_text(encoding="utf-8")
    src_hm = (PKG_DIR / "higher_moments.py").read_text(encoding="utf-8")
    src_box = (PKG_DIR / "box_certifier.py").read_text(encoding="utf-8")

    sources = {
        "exact_qi.py": src_exact,
        "dual_oracle.py": src_dual,
        "higher_moments.py": src_hm,
        "box_certifier.py": src_box,
    }
    require(file_name in sources, f"unknown module file {file_name}")
    orig = sources[file_name]
    count = orig.count(target_snippet)
    require(count == 1, f"mutation target in {file_name} occurred {count} times (expected 1): {target_snippet!r}")
    sources[file_name] = orig.replace(target_snippet, replacement_snippet, 1)

    pkg_name = "_mut_spectral_inertia"
    pkg_mod = types.ModuleType(pkg_name)
    pkg_mod.__path__ = []  # type: ignore[attr-defined]
    mod_names = (
        pkg_name,
        f"{pkg_name}.exact_qi",
        f"{pkg_name}.higher_moments",
        f"{pkg_name}.dual_oracle",
        f"{pkg_name}.box_certifier",
    )
    saved = {k: sys.modules.get(k) for k in mod_names}
    try:
        sys.modules[pkg_name] = pkg_mod
        loaded: dict[str, types.ModuleType] = {}
        for mod_short, fname in [
            ("exact_qi", "exact_qi.py"),
            ("higher_moments", "higher_moments.py"),
            ("dual_oracle", "dual_oracle.py"),
            ("box_certifier", "box_certifier.py"),
        ]:
            full_name = f"{pkg_name}.{mod_short}"
            m = types.ModuleType(full_name)
            m.__package__ = pkg_name
            sys.modules[full_name] = m
            exec(compile(sources[fname], f"<mutated:{fname}>", "exec"), m.__dict__)
            setattr(pkg_mod, mod_short, m)
            loaded[mod_short] = m
        return loaded
    finally:
        for k, v in saved.items():
            if v is None:
                sys.modules.pop(k, None)
            else:
                sys.modules[k] = v


def load_clean_package() -> dict[str, types.ModuleType]:
    # Load clean unmutated isolated copy using a harmless identity replacement on a comment-free unique token
    return load_mutated_package("exact_qi.py", "MAX_DIGIT_LEN = 4000", "MAX_DIGIT_LEN = 4000")


def run_all_mutants() -> dict[str, Any]:
    clean = load_clean_package()

    # Helper to construct clean valid matrices in a given module namespace
    def eye_str(n: int) -> list[list[str]]:
        return [["1" if i == j else "0" for j in range(n)] for i in range(n)]

    # Each mutant spec: (id, description, file_name, target, replacement, control_fn)
    # control_fn(mods) -> bool: MUST return True when the checker REJECTS the adversarial control
    # (or detects the corruption), and False when the mutant ACCEPTS/corrupts!
    mutants: list[tuple[str, str, str, str, str, Callable[[dict[str, types.ModuleType]], bool]]] = []

    def add_reject_mutant(
        mid: str,
        desc: str,
        fname: str,
        target: str,
        repl: str,
        call_fn: Callable[[dict[str, types.ModuleType]], Any],
    ) -> None:
        def control(mods: dict[str, types.ModuleType]) -> bool:
            CertErr = mods["exact_qi"].CertError
            try:
                call_fn(mods)
                return False  # Falsely accepted!
            except CertErr:
                return True  # Properly rejected with structured CertError!
            except Exception:
                return False  # Unhandled crash (e.g., KeyError / ValueError) instead of structured CertError -> KILLED!
        mutants.append((mid, desc, fname, target, repl, control))

    def add_verdict_mutant(
        mid: str,
        desc: str,
        fname: str,
        target: str,
        repl: str,
        check_fn: Callable[[dict[str, types.ModuleType]], bool],
    ) -> None:
        mutants.append((mid, desc, fname, target, repl, check_fn))

    # --- Group 1: R1 / R3 Strict Rational & JSON Parser Mutants (10 mutants) ---
    add_reject_mutant(
        "M01", "R3 bool-input guard in parse_strict_fraction removed",
        "exact_qi.py",
        '    if isinstance(val, bool):\n        raise CertError("REJECT_BOOL_INPUT", "bool is not a valid rational")',
        '    if False:\n        raise CertError("REJECT_BOOL_INPUT", "bool is not a valid rational")',
        lambda m: m["exact_qi"].parse_strict_fraction(True),
    )
    add_verdict_mutant(
        "M02", "R3 float-input guard in parse_strict_fraction removed",
        "exact_qi.py",
        '    if isinstance(val, float):\n        raise CertError("REJECT_FLOAT_INPUT", "float is forbidden in exact TCB")',
        '    if False:\n        raise CertError("REJECT_FLOAT_INPUT", "float is forbidden in exact TCB")',
        lambda m: _expect_code(
            m["exact_qi"].CertError,
            "REJECT_FLOAT_INPUT",
            lambda: m["exact_qi"].parse_strict_fraction(0.5),
        ),
    )
    add_reject_mutant(
        "M03", "R3 trailing-newline \\Z weakened to $ in _STRICT_FRAC_RE",
        "exact_qi.py",
        r'r"\A(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z"',
        r'r"\A(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?$"',
        lambda m: m["exact_qi"].parse_strict_fraction("1/2\n"),
    )
    add_reject_mutant(
        "M04", "R3 regex ASCII restriction weakened to allow Unicode digits",
        "exact_qi.py",
        '    r"\\A(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\\Z",\n    re.ASCII,',
        '    r"\\A(?:0|-?[1-9]\\d*)(?:/[1-9]\\d*)?\\Z",\n    0,',
        lambda m: m["exact_qi"].parse_strict_fraction("1\u0661/2\u0660"),
    )
    add_reject_mutant(
        "M05", "R3 digit-length DoS guard removed",
        "exact_qi.py",
        '    if len(val.lstrip("-")) > MAX_DIGIT_LEN:\n        raise CertError("OVERSIZED_RATIONAL_DIGITS", "digit limit exceeded")',
        '    if False:\n        raise CertError("OVERSIZED_RATIONAL_DIGITS", "digit limit exceeded")',
        lambda m: m["exact_qi"].parse_strict_fraction("1" * 4100),
    )
    add_reject_mutant(
        "M06", "R3 bool-rejection in parse_strict_int removed",
        "exact_qi.py",
        '    if isinstance(val, bool) or not isinstance(val, int):',
        '    if not isinstance(val, int):',
        lambda m: m["exact_qi"].parse_strict_int(True, min_value=0),
    )
    add_reject_mutant(
        "M07", "R3 min_value range guard in parse_strict_int removed (AUDIT-001 exploit #6)",
        "exact_qi.py",
        '    if min_value is not None and val < min_value:\n        raise CertError("INT_OUT_OF_RANGE", f"integer {val} < min {min_value}")',
        '    if False and min_value is not None and val < min_value:\n        raise CertError("INT_OUT_OF_RANGE", f"integer {val} < min {min_value}")',
        lambda m: m["dual_oracle"].certify_mode_a_hardened([[1]], [0], target_rank_gt=-5),
    )
    add_reject_mutant(
        "M08", "R3 JSON duplicate-key hook removed",
        "exact_qi.py",
        '            object_pairs_hook=reject_duplicate_keys,',
        '            object_pairs_hook=None,',
        lambda m: m["exact_qi"].parse_strict_json('{"a": 1, "a": 2}'),
    )
    add_reject_mutant(
        "M09", "R3 JSON float rejection hook removed",
        "exact_qi.py",
        '            parse_float=reject_float,',
        '            parse_float=None,',
        lambda m: m["exact_qi"].parse_strict_json('{"a": 0.5}'),
    )
    add_reject_mutant(
        "M10", "R3 JSON NaN/Infinity constant hook removed",
        "exact_qi.py",
        '            parse_constant=reject_constant,',
        '            parse_constant=None,',
        lambda m: m["exact_qi"].parse_strict_json('{"a": NaN}'),
    )

    # --- Group 2: Oracle 1 PLDL* & C M C* = D Structural Guards (14 mutants) ---
    add_reject_mutant(
        "M11", "R2 required-keys omission guard removed in PLDL cert",
        "dual_oracle.py",
        '    if not required_keys.issubset(keys):\n        missing = sorted(required_keys - keys)\n        raise CertError("MISSING_CERT_KEYS", f"missing required keys: {missing}")',
        '    if False:\n        missing = sorted(required_keys - keys)\n        raise CertError("MISSING_CERT_KEYS", f"missing required keys: {missing}")',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert({"M": [["1"]], "P": [0], "L": [["1"]]}),
    )
    add_reject_mutant(
        "M12", "Permutation duplicate-index guard removed (P=[0,0] on diag(1,-1) forges (1,0,1))",
        "dual_oracle.py",
        '    if len(set(P_perm)) != n:\n        raise CertError("INVALID_PERMUTATION_DUPLICATE", "P must be a bijection of 0..n-1")',
        '    if False:\n        raise CertError("INVALID_PERMUTATION_DUPLICATE", "P must be a bijection of 0..n-1")',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert(
            {"M": [["1", "0"], ["0", "-1"]], "P": [0, 0], "L": [["1", "0"], ["1", "1"]], "D": [["1", "0"], ["0", "0"]], "claim": [1, 0, 1]}
        ),
    )
    add_reject_mutant(
        "M13", "Unit diagonal of L guard removed",
        "dual_oracle.py",
        '        if L[i][i] != ONE:\n            raise CertError("L_NOT_UNIT_DIAGONAL", f"L[{i}][{i}] != 1")',
        '        if False:\n            raise CertError("L_NOT_UNIT_DIAGONAL", f"L[{i}][{i}] != 1")',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert(
            {"M": [["0", "0"], ["0", "1"]], "P": [0, 1], "L": [["0", "0"], ["0", "1"]], "D": eye_str(2), "claim": [2, 0, 0]}
        ),
    )
    add_reject_mutant(
        "M14", "Zero above diagonal of L guard removed (singular L=[[1,1],[1,1]])",
        "dual_oracle.py",
        '            if not L[i][j].is_zero():\n                raise CertError("L_NOT_LOWER_TRIANGULAR", f"nonzero upper entry L[{i}][{j}]")',
        '            if False:\n                raise CertError("L_NOT_LOWER_TRIANGULAR", f"nonzero upper entry L[{i}][{j}]")',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert(
            {"M": [["2", "2"], ["2", "2"]], "P": [0, 1], "L": [["1", "1"], ["1", "1"]], "D": eye_str(2), "claim": [2, 0, 0]}
        ),
    )
    add_reject_mutant(
        "M15", "Overlapping 2x2 blocks guard in D removed ([[1,1,0],[1,1,1],[0,1,1]])",
        "dual_oracle.py",
        '        if not D[i][i + 1].is_zero() and not D[i + 1][i + 2].is_zero():\n            raise CertError("D_OVERLAPPING_2X2_BLOCKS", f"overlapping 2x2 blocks at index {i}")',
        '        if False:\n            raise CertError("D_OVERLAPPING_2X2_BLOCKS", f"overlapping 2x2 blocks at index {i}")',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert(
            {"M": [["1", "1", "0"], ["1", "1", "1"], ["0", "1", "1"]], "P": [0, 1, 2], "L": eye_str(3),
             "D": [["1", "1", "0"], ["1", "1", "1"], ["0", "1", "1"]], "claim": [2, 0, 1]}
        ),
    )
    add_reject_mutant(
        "M16", "Band width guard |i-j|>1 on D removed",
        "dual_oracle.py",
        '            if abs(i - j) > 1 and not D[i][j].is_zero():\n                raise CertError("D_NOT_BLOCK_TRIDIAGONAL", f"nonzero entry outside band at ({i},{j})")',
        '            if False:\n                raise CertError("D_NOT_BLOCK_TRIDIAGONAL", f"nonzero entry outside band at ({i},{j})")',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert(
            {"M": [["1", "0", "2"], ["0", "1", "0"], ["2", "0", "1"]], "P": [0, 1, 2], "L": eye_str(3),
             "D": [["1", "0", "2"], ["0", "1", "0"], ["2", "0", "1"]], "claim": [3, 0, 0]}
        ),
    )
    add_reject_mutant(
        "M17", "PLDL* identity check removed",
        "dual_oracle.py",
        '    require_cert(PMP == LDL, "PLDL_IDENTITY_MISMATCH", "P * M * P* != L * D * L*")',
        '    require_cert(True, "PLDL_IDENTITY_MISMATCH", "P * M * P* != L * D * L*")',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert(
            {"M": [["-1", "0"], ["0", "-1"]], "P": [0, 1], "L": eye_str(2), "D": eye_str(2), "claim": [2, 0, 0]}
        ),
    )
    add_reject_mutant(
        "M18", "Claim mismatch check removed",
        "dual_oracle.py",
        '    if (cp, cn, cz) != computed:\n        raise CertError(',
        '    if False:\n        raise CertError(',
        lambda m: m["dual_oracle"].verify_congruence_pldl_cert(
            {"M": [["1", "0"], ["0", "-1"]], "P": [0, 1], "L": eye_str(2), "D": [["1", "0"], ["0", "-1"]], "claim": [2, 0, 0]}
        ),
    )
    add_reject_mutant(
        "M19", "C * C_inv == I invertibility check removed in C-cert",
        "dual_oracle.py",
        '    require_cert(prod_r == I, "C_NOT_INVERTIBLE", "C * C_inv != I")',
        '    require_cert(True, "C_NOT_INVERTIBLE", "C * C_inv != I")',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[1, 0], [0, -1]], [[1, 0], [0, 0]], [[1, 0], [0, 0]], [[1, 0], [0, 0]]
        ),
    )
    add_reject_mutant(
        "M20", "C * M * C* == D congruence identity check removed",
        "dual_oracle.py",
        '    require_cert(cong == D, "CONGRUENCE_IDENTITY_MISMATCH", "C * M * C* != D")',
        '    require_cert(True, "CONGRUENCE_IDENTITY_MISMATCH", "C * M * C* != D")',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[-1, 0], [0, -1]], [[1, 0], [0, 1]], [[1, 0], [0, 1]], [1, 1]
        ),
    )
    add_reject_mutant(
        "M21", "Diagonal D length mismatch guard removed (AUDIT-001 exploit #4)",
        "dual_oracle.py",
        '    elif isinstance(D_raw, (list, tuple)) and len(D_raw) != n and (len(D_raw) == 0 or not isinstance(D_raw[0], (list, tuple))):\n        raise CertError("D_DIM_MISMATCH", f"diagonal D length {len(D_raw)} != {n}")',
        '    elif isinstance(D_raw, (list, tuple)) and len(D_raw) != n and (len(D_raw) == 0 or not isinstance(D_raw[0], (list, tuple))):\n        D = cmat_zeros(n, n)',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[0, 0], [0, 0]], [[1, 0], [0, 1]], [[1, 0], [0, 1]], [0, 0, 5]
        ),
    )
    add_reject_mutant(
        "M22", "Size cap max_dim guard removed",
        "exact_qi.py",
        '    if n_rows > max_dim:\n        raise CertError("MATRIX_DIM_EXCEEDED", f"row count {n_rows} exceeds max_dim={max_dim}")',
        '    if False:\n        raise CertError("MATRIX_DIM_EXCEEDED", f"row count {n_rows} exceeds max_dim={max_dim}")',
        lambda m: m["exact_qi"].parse_matrix_qi([[1], [1]], max_dim=1, require_square=False),
    )
    add_reject_mutant(
        "M23", "Hermitian check on M removed in parse_hermitian_matrix (AUDIT-001 exploit #2)",
        "exact_qi.py",
        '    require_cert(is_hermitian(mat), "MATRIX_NOT_HERMITIAN", "matrix is not Hermitian")',
        '    require_cert(True, "MATRIX_NOT_HERMITIAN", "matrix is not Hermitian")',
        lambda m: m["exact_qi"].parse_hermitian_matrix([[1, 2], [0, 1]]),
    )
    add_reject_mutant(
        "M24", "D Hermitian check removed in _check_block_diagonal_hermitian_and_inertia",
        "dual_oracle.py",
        '    require_cert(is_hermitian(D), "D_NOT_HERMITIAN", "D must be Hermitian")',
        '    require_cert(True, "D_NOT_HERMITIAN", "D must be Hermitian")',
        lambda m: m["dual_oracle"]._check_block_diagonal_hermitian_and_inertia(
            [[m["exact_qi"].Qi(Fraction(1), Fraction(1))]]
        ),
    )

    # --- Group 3: 2x2 & 1x1 Block Inertia Table Sign Mutants (6 mutants) ---
    add_verdict_mutant(
        "M25", "2x2 det < 0 miscounted as (2, 0, 0)",
        "dual_oracle.py",
        '            if det < 0:\n                n_pos += 1\n                n_neg += 1',
        '            if det < 0:\n                n_pos += 2',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[0, 1], [1, 0]], [[1, 0], [0, 1]], [[1, 0], [0, 1]], [[0, 1], [1, 0]]
        ) == (1, 1, 0),
    )
    add_verdict_mutant(
        "M26", "2x2 det > 0, tr < 0 miscounted as (2, 0, 0)",
        "dual_oracle.py",
        '                elif tr < 0:\n                    n_neg += 2',
        '                elif tr < 0:\n                    n_pos += 2',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[-3, 1], [1, -3]], [[1, 0], [0, 1]], [[1, 0], [0, 1]], [[-3, 1], [1, -3]]
        ) == (0, 2, 0),
    )
    add_verdict_mutant(
        "M27", "2x2 det == 0, tr > 0 miscounted as (0, 1, 1)",
        "dual_oracle.py",
        '                if tr > 0:\n                    n_pos += 1\n                    n_zero += 1',
        '                if tr > 0:\n                    n_neg += 1\n                    n_zero += 1',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[1, 1], [1, 1]], [[1, 0], [0, 1]], [[1, 0], [0, 1]], [[1, 1], [1, 1]]
        ) == (1, 0, 1),
    )
    add_verdict_mutant(
        "M28", "2x2 det == 0, tr < 0 miscounted as (1, 0, 1)",
        "dual_oracle.py",
        '                elif tr < 0:\n                    n_neg += 1\n                    n_zero += 1',
        '                elif tr < 0:\n                    n_pos += 1\n                    n_zero += 1',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[-1, 1], [1, -1]], [[1, 0], [0, 1]], [[1, 0], [0, 1]], [[-1, 1], [1, -1]]
        ) == (0, 1, 1),
    )
    add_verdict_mutant(
        "M29", "1x1 zero block miscounted as positive",
        "dual_oracle.py",
        '            elif d < 0:\n                n_neg += 1\n            else:\n                n_zero += 1',
        '            elif d < 0:\n                n_neg += 1\n            else:\n                n_pos += 1',
        lambda m: m["dual_oracle"].verify_congruence_c_cert(
            [[0]], [[1]], [[1]], [0]
        ) == (0, 0, 1),
    )
    add_reject_mutant(
        "M30", "Dual-oracle disagreement check removed",
        "dual_oracle.py",
        '    require_cert(\n        inertia_1 == inertia_2,\n        "DUAL_ORACLE_DISAGREEMENT",',
        '    require_cert(\n        True,\n        "DUAL_ORACLE_DISAGREEMENT",',
        # Directly trigger disagreement by patching oracle2 inside the mutated namespace
        lambda m: (
            setattr(m["dual_oracle"], "oracle_faddeev_descartes_sturm", lambda *a, **kw: {"inertia": (0, 0, 1), "descartes_inertia": (0, 0, 1), "sturm_inertia": (0, 0, 1), "cayley_hamilton_verified": True}),
            m["dual_oracle"].verify_inertia_dual_oracle(
                {"M": [["1"]], "P": [0], "L": [["1"]], "D": [["1"]], "claim": [1, 0, 0]}, mode="pldl"
            ),
        ),
    )

    # --- Group 4: Mode B AUDIT-001 Critical Security Guards (2 mutants) ---
    # H = diag(10, 10), Q = diag(25, -11) => P = diag(-15, 21) (NOT PSD, yet u=6>0, t=14, S=200, R_opt=9!)
    # Removing p_neg == 0 allows forging rank >= 9 on a 2x2 matrix even with R_opt!
    add_reject_mutant(
        "M31", "CRITICAL AUDIT-001 exploit #1: P >= 0 (p_neg == 0) guard removed in Mode B",
        "dual_oracle.py",
        '    require_cert(p_neg == 0, "P_NOT_PSD", f"P = H - Q has {p_neg} negative eigenvalues (must be 0)")',
        '    require_cert(True, "P_NOT_PSD", f"P = H - Q has {p_neg} negative eigenvalues (must be 0)")',
        lambda m: m["dual_oracle"].certify_mode_b_hardened(
            [[10, 0], [0, 10]], [[25, 0], [0, -11]],
            [[1, 0], [0, 1]], [[1, 0], [0, 1]], [25, -11],
            [[1, 0], [0, 1]], [[1, 0], [0, 1]], [-15, 21],
            target_rank_gt=8, use_ropt=True,
        ),
    )
    add_reject_mutant(
        "M32", "AUDIT-001 exploit #3: len(H) == len(Q) guard removed in Mode B",
        "dual_oracle.py",
        '    require_cert(len(H) == len(Q), "H_Q_DIM_MISMATCH", f"len(H)={len(H)} != len(Q)={len(Q)}")',
        '    require_cert(True, "H_Q_DIM_MISMATCH", f"len(H)={len(H)} != len(Q)={len(Q)}")',
        lambda m: m["dual_oracle"].certify_mode_b_hardened(
            [[1, 0, 0], [0, 1, 0], [0, 0, 1]], [[0, 0], [0, 0]],
            [[1, 0], [0, 1]], [[1, 0], [0, 1]], [0, 0],
            [[1, 0], [0, 1]], [[1, 0], [0, 1]], [1, 1],
            target_rank_gt=0,
        ) if False else (_ for _ in ()).throw(m["exact_qi"].CertError("SKIP", "placeholder")),
    )
    # Wait! In M32, cmat_sub(H, Q) ALSO checks dims! So to isolate the H_Q_DIM_MISMATCH guard cleanly,
    # check the specific error code! Replace M32 cleanly below:
    mutants.pop()
    add_verdict_mutant(
        "M32", "AUDIT-001 exploit #3: H_Q_DIM_MISMATCH guard removed in Mode B",
        "dual_oracle.py",
        '    require_cert(len(H) == len(Q), "H_Q_DIM_MISMATCH", f"len(H)={len(H)} != len(Q)={len(Q)}")',
        '    require_cert(True, "H_Q_DIM_MISMATCH", f"len(H)={len(H)} != len(Q)={len(Q)}")',
        lambda m: (
            (lambda: (
                m["dual_oracle"].certify_mode_b_hardened(
                    [[1, 0, 0], [0, 1, 0], [0, 0, 1]], [[0, 0], [0, 0]],
                    [[1, 0], [0, 1]], [[1, 0], [0, 1]], [0, 0],
                    [[1, 0], [0, 1]], [[1, 0], [0, 1]], [1, 1],
                    target_rank_gt=0,
                )
            ))
        ) and _expect_code(
            m["exact_qi"].CertError,
            "H_Q_DIM_MISMATCH",
            lambda: m["dual_oracle"].certify_mode_b_hardened(
                [[1, 0, 0], [0, 1, 0], [0, 0, 1]], [[0, 0], [0, 0]],
                [[1, 0], [0, 1]], [[1, 0], [0, 1]], [0, 0],
                [[1, 0], [0, 1]], [[1, 0], [0, 1]], [1, 1],
                target_rank_gt=0,
            ),
        ),
    )

    # --- Group 5: Track A Higher-Moment Certificate Guards (4 mutants) ---
    S_sample = {1: Fraction(2), 2: Fraction(2), 3: Fraction(2), 4: Fraction(2)}
    add_reject_mutant(
        "M33", "Theorem A2 non-negative witness a_k >= 0 guard removed",
        "higher_moments.py",
        '        require_cert(ak >= 0, "NEGATIVE_HANKEL_COEFF", f"a_{idx} = {ak} < 0 violates phi(lam)<=0 on lam<=0")',
        '        require_cert(True, "NEGATIVE_HANKEL_COEFF", f"a_{idx} = {ak} < 0 violates phi(lam)<=0 on lam<=0")',
        lambda m: m["higher_moments"].certify_stieltjes_hankel_2m(S_sample, 0, [Fraction(1), Fraction(-1)]),
    )
    add_verdict_mutant(
        "M34", "Theorem A3 x0 > 0 guard removed",
        "higher_moments.py",
        '    require_cert(x0_f > 0, "INVALID_PEAK_X0", "Theorem A3 requires x0 > 0")',
        '    require_cert(True, "INVALID_PEAK_X0", "Theorem A3 requires x0 > 0")',
        lambda m: _expect_code(
            m["exact_qi"].CertError,
            "INVALID_PEAK_X0",
            lambda: m["higher_moments"].certify_noise_annihilating_quartic(S_sample, 0, Fraction(-1), Fraction(4)),
        ),
    )
    add_reject_mutant(
        "M35", "Theorem A3 tau >= 0 guard removed",
        "higher_moments.py",
        '    require_cert(tau_f >= 0, "INVALID_TAU", "Theorem A3 requires tau >= 0")',
        '    require_cert(True, "INVALID_TAU", "Theorem A3 requires tau >= 0")',
        lambda m: m["higher_moments"].certify_noise_annihilating_quartic(S_sample, 0, Fraction(1), Fraction(-1, 2)),
    )
    add_reject_mutant(
        "M36", "Theorem A4 gamma1 >= 0 monotonicity guard removed",
        "higher_moments.py",
        '    require_cert(g1_f >= 0, "A4_NEGATIVE_GAMMA1", "requires gamma1 >= 0")',
        '    require_cert(True, "A4_NEGATIVE_GAMMA1", "requires gamma1 >= 0")',
        lambda m: m["higher_moments"].certify_weighted_quartic_weyl(
            S_sample, Fraction(-10), Fraction(0), 1, s=Fraction(1), p=Fraction(1), gamma1=Fraction(-1), gamma3=Fraction(0), kappa=Fraction(1)
        ),
    )

    # --- Group 6: Track B Symbolic Hermitianity Guards (AUDIT-015) & Canonical Lowest-Terms R3 Guard (5 mutants) ---
    def _build_poly_helpers(m: dict[str, types.ModuleType]):
        bc = m["box_certifier"]
        eq = m["exact_qi"]
        x = bc.MultiPoly.var(1, 0)
        one = bc.MultiPoly.const(1, 1)
        z = bc.MultiPoly(1)
        i_u = bc.MultiPoly.const(1, eq.Qi(Fraction(0), Fraction(1)))
        return bc, x, one, z, i_u

    add_reject_mutant(
        "M37", "AUDIT-015: PolyMatrix symbolic real-diagonal guard removed ([[1+ix,0],[0,1]])",
        "box_certifier.py",
        '                if coef.im != 0:\n                    raise CertError(\n                        "POLYMAT_DIAG_NONREAL",',
        '                if False:\n                    raise CertError(\n                        "POLYMAT_DIAG_NONREAL",',
        lambda m: (lambda bc, x, one, z, i_u: bc.certify_hermitian_box(
            bc.PolyMatrix(1, [[one + i_u * x, z], [z, one]]),
            [(Fraction(-1, 2), Fraction(1, 2))],
        ))(*_build_poly_helpers(m)),
    )
    add_reject_mutant(
        "M38", "AUDIT-015: PolyMatrix symbolic off-diagonal conjugate guard removed ([[1,0],[100x,1]])",
        "box_certifier.py",
        '                if self.entries[i][j].terms != self.entries[j][i].conj().terms:\n                    raise CertError(\n                        "POLYMAT_NOT_SYMBOLICALLY_HERMITIAN",',
        '                if False:\n                    raise CertError(\n                        "POLYMAT_NOT_SYMBOLICALLY_HERMITIAN",',
        lambda m: (lambda bc, x, one, z, i_u: bc.certify_hermitian_box(
            bc.PolyMatrix(1, [[one, z], [100 * x, one]]),
            [(Fraction(-1, 2), Fraction(1, 2))],
        ))(*_build_poly_helpers(m)),
    )
    add_reject_mutant(
        "M39", "AUDIT-015: RatMatrix symbolic real-diagonal guard removed ([[(1+ix)/1,0],[0,1/1]])",
        "box_certifier.py",
        '                if coef.im != 0:\n                    raise CertError(\n                        "RATMAT_DIAG_NONREAL",',
        '                if False:\n                    raise CertError(\n                        "RATMAT_DIAG_NONREAL",',
        lambda m: (lambda bc, x, one, z, i_u: bc.certify_hermitian_box(
            bc.RatMatrix(1, [[one + i_u * x, z], [z, one]], [[one, one], [one, one]]),
            [(Fraction(-1, 2), Fraction(1, 2))],
        ))(*_build_poly_helpers(m)),
    )
    add_reject_mutant(
        "M40", "AUDIT-015: RatMatrix symbolic off-diagonal conjugate guard removed ([[1/1,0],[100x/1,1/1]])",
        "box_certifier.py",
        '                if lhs.terms != rhs.terms:\n                    raise CertError(\n                        "RATMAT_NOT_SYMBOLICALLY_HERMITIAN",',
        '                if False:\n                    raise CertError(\n                        "RATMAT_NOT_SYMBOLICALLY_HERMITIAN",',
        lambda m: (lambda bc, x, one, z, i_u: bc.certify_hermitian_box(
            bc.RatMatrix(1, [[one, z], [100 * x, one]], [[one, one], [one, one]]),
            [(Fraction(-1, 2), Fraction(1, 2))],
        ))(*_build_poly_helpers(m)),
    )
    add_reject_mutant(
        "M41", "AUDIT-016 R3 hygiene: lowest-terms canonical rational guard removed (rejects 2/4, 3/1, 0/5)",
        "exact_qi.py",
        '        if den_i == 1 or math.gcd(abs(num_i), den_i) != 1:\n            raise CertError("NON_CANONICAL_RATIONAL", f"rational string not in lowest terms: {val!r}")',
        '        if False:\n            raise CertError("NON_CANONICAL_RATIONAL", f"rational string not in lowest terms: {val!r}")',
        lambda m: m["exact_qi"].parse_strict_fraction("2/4"),
    )

    results = []
    killed = 0
    survivors = []

    for mid, desc, fname, target, repl, control_fn in mutants:
        # 1. Control MUST pass on clean unmutated code!
        clean_ok = control_fn(clean)
        require(clean_ok, f"{mid} ({desc}) control FAILED on CLEAN unmutated code!")

        # 2. Control MUST FAIL on mutated code (proving mutant is KILLED)!
        mut_mods = load_mutated_package(fname, target, repl)
        mut_ok = control_fn(mut_mods)
        is_killed = not mut_ok
        if is_killed:
            killed += 1
        else:
            survivors.append({"id": mid, "desc": desc})
        results.append({"id": mid, "status": "KILLED" if is_killed else "SURVIVED", "desc": desc})

    return {
        "total_mutants": len(mutants),
        "killed": killed,
        "survivors": len(survivors),
        "kill_rate_pct": round(100.0 * killed / len(mutants), 2),
        "survivor_details": survivors,
        "results": results,
    }


def _expect_code(exc_cls: type[Exception], expected_code: str, fn: Callable[[], Any]) -> bool:
    try:
        fn()
        return False
    except exc_cls as exc:
        return getattr(exc, "code", None) == expected_code


def main() -> None:
    report = run_all_mutants()
    print(json.dumps(report, indent=2))
    if report["survivors"] != 0:
        sys.exit(f"MUTATION SUITE FAILED: {report['survivors']} survivors")


if __name__ == "__main__":
    main()
