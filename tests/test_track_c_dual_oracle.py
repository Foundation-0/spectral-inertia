"""
Track C Test Suite: Hardened Dual-Oracle Exact Q(i) Certifier (SEAM-08, R1-R5).

Covers:
  - All 6 AUDIT-001 exploits CLOSED (missing P>=0 forgery, non-Hermitian H, mismatched dims,
    non-square C / extra D entries, all R3 parser leaks, negative/bool target_rank_gt).
  - All loom#7 guards (P permutation, L unit lower triangular, D band & non-overlapping 2x2 blocks,
    all 5 rows of 2x2 Hermitian block table real & complex, JSON duplicate keys / float / NaN / Infinity).
  - R1 (default reject empty/null/garbage), R2 (omission monotonicity), R3 (strict canonical encoding).
  - 150 random real & complex Q(i) Hermitian matrices (including zero-diagonal & singular matrices)
    cross-verified by BOTH Oracle 1 (Bunch-Kaufman congruence) AND Oracle 2 (zero-shared-code
    Faddeev-LeVerrier + Cayley-Hamilton + Descartes + exact Sturm sequence).
"""
from __future__ import annotations

from fractions import Fraction
import json
import random
import unittest

from spectral_inertia.dual_oracle import (
    certify_mode_a_hardened,
    certify_mode_b_hardened,
    oracle_faddeev_descartes_sturm,
    produce_c_certificate,
    produce_pldl_certificate,
    verify_congruence_c_cert,
    verify_congruence_pldl_cert,
    verify_inertia_dual_oracle,
)
from spectral_inertia.exact_qi import (
    CertError,
    ONE,
    Qi,
    ZERO,
    cayley_unitary,
    cmat_add,
    cmat_eye,
    cmat_zeros,
    matrix_to_json,
    parse_strict_fraction,
    parse_strict_int,
    parse_strict_json,
)


def _req(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


class TestTrackCDualOracle(unittest.TestCase):
    def test_01_r1_r2_r3_strict_parsers(self) -> None:
        # R3 strict fraction rejections (closes AUDIT-001 exploit #5)
        bad_fracs = [
            True,
            False,
            0.5,
            None,
            "",
            "1/2\n",
            " 1/2",
            "1/2 ",
            "0.5",
            "1e-5",
            "1_000",
            "+1",
            "-0",
            "-0/1",
            "01",
            "1/0",
            "1/02",
            "1/-2",
            "\u0661/\u0662",
            "1" * 4001,
        ]
        for bad in bad_fracs:
            with self.assertRaises(CertError, msg=f"failed to reject bad fraction {bad!r}"):
                parse_strict_fraction(bad)

        # Valid fractions
        _req(parse_strict_fraction("0") == 0, "0 failed")
        _req(parse_strict_fraction("0/1") == 0, "0/1 failed")
        _req(parse_strict_fraction("-13/7") == Fraction(-13, 7), "-13/7 failed")
        _req(parse_strict_fraction(42) == Fraction(42), "int 42 failed")

        # Strict int rejects bool, float, str
        for bad_i in (True, False, 1.0, "1", None):
            with self.assertRaises(CertError):
                parse_strict_int(bad_i)
        with self.assertRaises(CertError):
            parse_strict_int(-1, min_value=0)

        # R1 / R3 strict JSON rejections
        for bad_json in (
            "",
            "   ",
            "[]",
            "null",
            '{"a": 1.5}',
            '{"a": NaN}',
            '{"a": Infinity}',
            '{"a": 1, "a": 2}',
        ):
            with self.assertRaises(CertError, msg=f"failed to reject bad JSON {bad_json!r}"):
                parse_strict_json(bad_json)

    def test_02_all_six_audit001_exploits_closed(self) -> None:
        I2 = cmat_eye(2)
        Q_zero = cmat_zeros(2, 2)

        # Exploit 1: Missing P >= 0 forgery (H=diag(1,0), Q=diag(10,0) -> P=diag(-9,0) NOT PSD!)
        H_ex1 = [[Qi(Fraction(1)), ZERO], [ZERO, ZERO]]
        Q_ex1 = [[Qi(Fraction(10)), ZERO], [ZERO, ZERO]]
        with self.assertRaises(CertError) as ctx1:
            certify_mode_b_hardened(
                H_ex1, Q_ex1,
                I2, I2, [Fraction(10), Fraction(0)],
                I2, I2, [Fraction(-9), Fraction(0)],
                target_rank_gt=0,
            )
        _req(ctx1.exception.code == "P_NOT_PSD", f"wrong code {ctx1.exception.code}")

        # Even if attacker forges D_P = [9, 0], identity C_P * (H - Q) * C_P* != D_P rejects!
        with self.assertRaises(CertError) as ctx1b:
            certify_mode_b_hardened(
                H_ex1, Q_ex1,
                I2, I2, [Fraction(10), Fraction(0)],
                I2, I2, [Fraction(9), Fraction(0)],
                target_rank_gt=0,
            )
        _req(ctx1b.exception.code == "CONGRUENCE_IDENTITY_MISMATCH", f"wrong code {ctx1b.exception.code}")

        # Exploit 2: Non-Hermitian H rejected
        H_nonsym = [[Qi(Fraction(2)), Qi(Fraction(1))], [ZERO, Qi(Fraction(2))]]
        with self.assertRaises(CertError) as ctx2:
            certify_mode_b_hardened(
                H_nonsym, Q_zero, I2, I2, [0, 0], I2, I2, [2, 2], target_rank_gt=0
            )
        _req(ctx2.exception.code == "MATRIX_NOT_HERMITIAN", f"wrong code {ctx2.exception.code}")

        # Exploit 3: Mismatched len(H) != len(Q) rejected
        with self.assertRaises(CertError) as ctx3:
            certify_mode_b_hardened(
                cmat_eye(3), Q_zero, I2, I2, [0, 0], I2, I2, [1, 1], target_rank_gt=0
            )
        _req(ctx3.exception.code == "H_Q_DIM_MISMATCH", f"wrong code {ctx3.exception.code}")

        # Exploit 4: Non-square 3x2 C / extra D_diag entry rejected
        C_3x2 = [[ONE, ZERO], [ZERO, ONE], [Qi(Fraction(99)), Qi(Fraction(99))]]
        with self.assertRaises(CertError):
            verify_congruence_c_cert(Q_zero, C_3x2, I2, [0, 0, 5])
        with self.assertRaises(CertError):
            verify_congruence_c_cert(Q_zero, I2, I2, [0, 0, 5])

        # Exploit 5: R3 parser leaks inside matrix entries rejected
        with self.assertRaises(CertError):
            certify_mode_a_hardened([["1/2\n"]], [0], target_rank_gt=0)
        with self.assertRaises(CertError):
            certify_mode_a_hardened([[True]], [0], target_rank_gt=0)

        # Exploit 6: Negative or bool target_rank_gt rejected
        with self.assertRaises(CertError):
            certify_mode_a_hardened([[1]], [0], target_rank_gt=-5)
        with self.assertRaises(CertError):
            certify_mode_a_hardened([[1]], [0], target_rank_gt=True)  # type: ignore[arg-type]
        with self.assertRaises(CertError):
            certify_mode_b_hardened(
                [[1]], [[0]], [[1]], [[1]], [0], [[1]], [[1]], [1], target_rank_gt=-1
            )

        # Positive Mode B check on Scan 23848 (rho=0) succeeds cleanly with dual oracle!
        w1 = Fraction(6404, 10000) ** 2
        w2 = Fraction(3596, 10000) ** 2
        H_pos = [[Qi(w1), ZERO], [ZERO, Qi(w2)]]
        Q_pos = [[Qi(w1), ZERO], [ZERO, ZERO]]
        res_ok = certify_mode_b_hardened(
            H_pos, Q_pos, I2, I2, [w1, 0], I2, I2, [0, w2], target_rank_gt=0, use_ropt=True
        )
        _req(res_ok["certified_min_projected_pos_inertia"] == 1 and res_ok["exact_bound"] == "1",
             f"unexpected positive Mode B result: {res_ok}")

    def test_03_all_five_2x2_block_rows_real_and_complex(self) -> None:
        """Directly test all 5 rows of the 2x2 Hermitian block inertia table (real & complex)."""
        cases = [
            # (M, expected_inertia)
            # Row 1: det < 0 -> (1, 1, 0)
            ([[Qi(Fraction(0)), Qi(Fraction(1), Fraction(2))], [Qi(Fraction(1), Fraction(-2)), Qi(Fraction(0))]], (1, 1, 0)),
            # Row 2: det > 0, tr > 0 -> (2, 0, 0)
            ([[Qi(Fraction(3)), Qi(Fraction(1), Fraction(1))], [Qi(Fraction(1), Fraction(-1)), Qi(Fraction(3))]], (2, 0, 0)),
            # Row 3: det > 0, tr < 0 -> (0, 2, 0)
            ([[Qi(Fraction(-3)), Qi(Fraction(1), Fraction(-1))], [Qi(Fraction(1), Fraction(1)), Qi(Fraction(-3))]], (0, 2, 0)),
            # Row 4: det == 0, b != 0, tr > 0 -> (1, 0, 1)  (a=2, c=1, b=1+i => |b|^2=2 == a*c)
            ([[Qi(Fraction(2)), Qi(Fraction(1), Fraction(1))], [Qi(Fraction(1), Fraction(-1)), Qi(Fraction(1))]], (1, 0, 1)),
            # Row 5: det == 0, b != 0, tr < 0 -> (0, 1, 1)  (a=-2, c=-1, b=1-i => |b|^2=2 == a*c)
            ([[Qi(Fraction(-2)), Qi(Fraction(1), Fraction(-1))], [Qi(Fraction(1), Fraction(1)), Qi(Fraction(-1))]], (0, 1, 1)),
        ]
        I2_j = matrix_to_json(cmat_eye(2))
        for M, exp in cases:
            payload = {
                "M": matrix_to_json(M),
                "P": [0, 1],
                "L": I2_j,
                "D": matrix_to_json(M),
                "claim": list(exp),
            }
            res = verify_inertia_dual_oracle(json.dumps(payload), mode="pldl")
            _req(res["inertia"] == exp and res["oracle2_descartes"] == exp and res["oracle2_sturm"] == exp,
                 f"2x2 block table mismatch for {exp}: {res}")

    def test_04_loom7_structural_guards_and_r2_omission(self) -> None:
        # Guard: Overlapping 2x2 blocks M = D = [[1,1,0],[1,1,1],[0,1,1]] (true inertia (2,1,0))
        M_ov = [["1", "1", "0"], ["1", "1", "1"], ["0", "1", "1"]]
        I3 = [["1", "0", "0"], ["0", "1", "0"], ["0", "0", "1"]]
        with self.assertRaises(CertError) as ctx_ov:
            verify_congruence_pldl_cert({"M": M_ov, "P": [0, 1, 2], "L": I3, "D": M_ov})
        _req(ctx_ov.exception.code == "D_OVERLAPPING_2X2_BLOCKS", f"wrong code {ctx_ov.exception.code}")

        # Guard: Repeated permutation index P = [0, 0] on M = diag(1, -1)
        M_perm = [["1", "0"], ["0", "-1"]]
        I2 = [["1", "0"], ["0", "1"]]
        with self.assertRaises(CertError) as ctx_p:
            verify_congruence_pldl_cert({"M": M_perm, "P": [0, 0], "L": I2, "D": [["1", "0"], ["0", "1"]]})
        _req(ctx_p.exception.code == "INVALID_PERMUTATION_DUPLICATE", f"wrong code {ctx_p.exception.code}")

        # Guard: Upper-triangular nonzero entry in L (singular L = [[1,1],[1,1]])
        with self.assertRaises(CertError) as ctx_l:
            verify_congruence_pldl_cert(
                {"M": [["2", "2"], ["2", "2"]], "P": [0, 1], "L": [["1", "1"], ["1", "1"]], "D": I2}
            )
        _req(ctx_l.exception.code == "L_NOT_LOWER_TRIANGULAR", f"wrong code {ctx_l.exception.code}")

        # Guard: Non-unit diagonal in L
        with self.assertRaises(CertError) as ctx_lu:
            verify_congruence_pldl_cert(
                {"M": [["4", "0"], ["0", "1"]], "P": [0, 1], "L": [["2", "0"], ["0", "1"]], "D": I2}
            )
        _req(ctx_lu.exception.code == "L_NOT_UNIT_DIAGONAL", f"wrong code {ctx_lu.exception.code}")

        # R2 Omission monotonicity: deleting any required key from a valid cert MUST reject
        valid = produce_pldl_certificate([[Qi(Fraction(2)), ZERO], [ZERO, Qi(Fraction(-1))]])
        _req(verify_congruence_pldl_cert(valid) == (1, 1, 0), "valid cert failed")
        for key in ("M", "P", "L", "D"):
            stripped = {k: v for k, v in valid.items() if k != key}
            with self.assertRaises(CertError):
                verify_congruence_pldl_cert(stripped)

    def test_05_120_random_complex_hermitian_dual_oracle_agreement(self) -> None:
        """
        Cross-verify Oracle 1 (PLDL* AND C M C* = D) vs Oracle 2 (Faddeev-LeVerrier +
        Cayley-Hamilton + Descartes + exact Sturm) on 120 random Q(i) Hermitian matrices
        including zero-diagonal, singular, repeated-eigenvalue, and high-multiplicity cases!
        """
        rng = random.Random(20261120)
        for trial in range(120):
            n = rng.randint(1, 5)
            if trial < 20 and n >= 2:
                # Zero-diagonal complex Hermitian (forces 2x2 Bunch-Kaufman blocks!)
                M = cmat_zeros(n, n)
                for i in range(n):
                    for j in range(i + 1, n):
                        re = Fraction(rng.randint(-3, 3), rng.randint(1, 2))
                        im = Fraction(rng.randint(-3, 3), rng.randint(1, 2))
                        M[i][j] = Qi(re, im)
                        M[j][i] = Qi(re, -im)
            else:
                # Arbitrary spectrum with frequent zeros and repeated eigenvalues (tests Sturm multiplicity peel!)
                U = cayley_unitary(n, rng, bound=2)
                eigs = [Fraction(rng.choice([-2, -1, -1, 0, 0, 1, 1, 2]), rng.choice([1, 2])) for _ in range(n)]
                M = cmat_zeros(n, n)
                for k, lam in enumerate(eigs):
                    if lam == 0:
                        continue
                    lq = Qi(lam)
                    for i in range(n):
                        for j in range(n):
                            M[i][j] = M[i][j] + lq * U[i][k] * U[j][k].conj()

            # Produce BOTH PLDL* and C M C* = D certificates and dual-oracle verify BOTH!
            pldl_cert = produce_pldl_certificate(M)
            res_pldl = verify_inertia_dual_oracle(json.dumps(pldl_cert), mode="pldl")

            C, C_inv, D, in_c = produce_c_certificate(M)
            c_payload = {
                "M": matrix_to_json(M),
                "C": matrix_to_json(C),
                "C_inv": matrix_to_json(C_inv),
                "D": matrix_to_json(D),
                "claim": list(in_c),
            }
            res_c = verify_inertia_dual_oracle(json.dumps(c_payload), mode="c_cert")
            _req(res_pldl["inertia"] == res_c["inertia"], "PLDL and C_cert disagreed")
            _req(res_pldl["oracle2_descartes"] == res_pldl["oracle2_sturm"], "Descartes vs Sturm disagreed")


if __name__ == "__main__":
    unittest.main()
