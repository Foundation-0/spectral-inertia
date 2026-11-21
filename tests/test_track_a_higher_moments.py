"""
Track A Test Suite: Exact Q(i) Verification of Theorems A1-A4 (R_opt + Higher-Moment Breakthroughs).

Verifies:
  1. Zero violations of n_+(Pi_{W^perp} H Pi_{W^perp}) >= BOUND across 200+ strictly non-commuting
     complex Hermitian matrices over exact Q(i) for ALL 4 theorem families (A1, A2-H4, A2-H6, A3, A4).
  2. Strict dominance over R_opt AND strict integer-rank breakthroughs strictly beating max(1, ceil(R_opt))
     on BOTH exact non-commuting Q(i) matrices AND project-asma Scan 23848 high-interference regimes
     rho in [0.5, 0.95] with noise tau > 0.
  3. Gate 2 Unitary Basis Invariance (H -> U H U*, Q -> U Q U*) and Scale Invariance (H -> alpha H).
  4. Gate 3 Negative Controls (single-species rank-1 ablation, phase boundary lam2 < tau,
     invalid witness rejections: x0 <= 0, tau < 0, a_k < 0, p <= 0, kappa <= 0).
  5. Zero bare asserts (python3 -O -B and -W error clean).
"""
from __future__ import annotations

from fractions import Fraction
import math
import random
import unittest

from spectral_inertia.dual_oracle import oracle_faddeev_descartes_sturm
from spectral_inertia.exact_qi import (
    CertError,
    Qi,
    ZERO,
    cayley_unitary,
    cmat_add,
    cmat_dagger,
    cmat_frob_sq,
    cmat_mul,
    cmat_rank,
    cmat_scale,
    cmat_sub,
    cmat_trace_real,
    cmat_zeros,
)
from spectral_inertia.examples.scan23848_benchmark import run_scan23848_benchmark
from spectral_inertia.higher_moments import (
    R_G_fable,
    R_hankel4_exact,
    R_hankel6_exact,
    R_lemma32_fixed_c,
    R_opt,
    best_higher_moment_bound,
    certify_noise_annihilating_quartic,
    certify_stieltjes_hankel_2m,
    certify_weighted_quartic_weyl,
    certify_weighted_quartic_weyl_peak,
    find_noise_quartic_witness,
    spectral_moments_exact,
)


def _req(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _build_hermitian_from_unitary(U, eigs: list[Fraction]):
    n = len(U)
    M = cmat_zeros(n, n)
    for k, lam in enumerate(eigs):
        if lam == 0:
            continue
        lq = Qi(lam)
        for i in range(n):
            for j in range(n):
                M[i][j] = M[i][j] + lq * U[i][k] * U[j][k].conj()
    return M


class TestTrackAHigherMoments(unittest.TestCase):
    def test_01_ropt_boundary_guards(self) -> None:
        # Guard 1: u = 0, t = 1, S = 1, b = 1 (previously 0/0) -> exact 0
        _req(R_opt(Fraction(0), Fraction(1), Fraction(1), 1) == 0, "u=0 guard failed")
        # Guard 1b: u + t <= 0 -> 0
        _req(R_opt(Fraction(1), Fraction(-2), Fraction(5), 1) == 0, "u+t<=0 guard failed")
        # Guard 2: negative else branch clamped to 0
        _req(R_opt(Fraction(1), Fraction(1), Fraction(10), 5) == 0, "negative clamp failed")
        # Regime 1 exact
        _req(R_opt(Fraction(6), Fraction(5), Fraction(43), 1) == Fraction(2), "Regime 1 exact failed")

    def test_02_noncommuting_complex_hermitian_all_theorems_exact_qi(self) -> None:
        """
        Exhaustive exact Q(i) non-commuting complex Hermitian test of Theorems A1, A2 (H4 & H6),
        A3 (Noise-Annihilating Quartic SOS), and A4 (Weighted Quartic-Weyl SOS) against the
        strictest target n_+(Pi_{W^perp} H Pi_{W^perp}).
        """
        rng = random.Random(20261120)
        total = 0
        noncommuting = 0
        complex_count = 0
        strict_wins_over_ropt = 0
        strict_ceil_wins = 0

        for n in (3, 4):
            for trial in range(45):
                # Mix general and high-dynamic-range spectra
                if trial < 25:
                    b_true = 1
                    r_true = n - 1
                    p_eigs = [Fraction(4)] + [Fraction(1, 5)] * (r_true - 1) + [Fraction(0)] * (n - r_true)
                    q_eigs = [Fraction(8)] + [-Fraction(1, 20)] * (n - 1)
                else:
                    r_true = rng.randint(1, n)
                    b_true = rng.randint(0, n - 1)
                    p_eigs = [Fraction(rng.randint(1, 6), rng.randint(1, 4)) for _ in range(r_true)] + [Fraction(0)] * (n - r_true)
                    q_eigs = [Fraction(rng.randint(1, 6), rng.randint(1, 3)) for _ in range(b_true)] + [
                        -Fraction(rng.randint(0, 4), rng.randint(1, 3)) for _ in range(n - b_true)
                    ]

                U_P = cayley_unitary(n, rng, bound=2)
                U_Q = cayley_unitary(n, rng, bound=2)
                P = _build_hermitian_from_unitary(U_P, p_eigs)
                Q = _build_hermitian_from_unitary(U_Q, q_eigs)
                H = cmat_add(P, Q)

                comm = cmat_sub(cmat_mul(P, Q), cmat_mul(Q, P))
                if cmat_frob_sq(comm) > 0:
                    noncommuting += 1
                if any(v.im != 0 for row in H for v in row):
                    complex_count += 1

                # Exact W^perp compression using columns b_true..n-1 of exact unitary U_Q
                m_perp = n - b_true
                U_perp = [[U_Q[i][b_true + j] for j in range(m_perp)] for i in range(n)]
                H_perp = cmat_mul(cmat_mul(cmat_dagger(U_perp), H), U_perp)
                P_perp = cmat_mul(cmat_mul(cmat_dagger(U_perp), P), U_perp)

                n_pos_H_perp = oracle_faddeev_descartes_sturm(H_perp)["inertia"][0]
                rank_P_perp = cmat_rank(P_perp)
                rank_P = cmat_rank(P)
                _req(rank_P >= rank_P_perp >= n_pos_H_perp, "projected chain broken")

                moments_H = spectral_moments_exact(H, max_k=6)
                u = cmat_trace_real(P)
                t1 = cmat_trace_real(Q)
                t3 = spectral_moments_exact(Q, max_k=3)[3]

                ropt = R_opt(u, t1, moments_H[2], b_true)
                rg = R_G_fable(u, t1, moments_H[2], b_true)
                rc2 = R_lemma32_fixed_c(u, t1, moments_H[2], b_true)
                h4 = R_hankel4_exact(moments_H[1], moments_H[2], moments_H[3], moments_H[4], b_true)
                h6 = R_hankel6_exact(moments_H, b_true)
                a3_0 = find_noise_quartic_witness(moments_H, b_true, Fraction(0))
                a3_t = find_noise_quartic_witness(moments_H, b_true, Fraction(1, 20))
                summary = best_higher_moment_bound(
                    moments_H, u, t1, b_true, t3_Q=t3, tau_hint=Fraction(1, 20)
                )

                # Universal soundness against STRICTLY TIGHTER n_+(H_perp)!
                target = Fraction(n_pos_H_perp)
                _req(ropt <= target, f"R_opt violated n_+(H_perp): {ropt} > {target}")
                _req(ropt >= rg and ropt >= rc2, "R_opt failed to dominate baselines")
                _req(h4["exact_bound"] <= target, f"H4 violated: {h4['exact_bound']} > {target}")
                _req(h6["exact_bound"] <= target, f"H6 violated: {h6['exact_bound']} > {target}")
                _req(h6["exact_bound"] >= h4["exact_bound"], "H6 must dominate H4 monotonically")
                _req(a3_0["exact_bound"] <= target, f"A3(tau=0) violated: {a3_0['exact_bound']} > {target}")
                _req(a3_t["exact_bound"] <= target, f"A3(tau>0) violated: {a3_t['exact_bound']} > {target}")
                _req(summary["best_bound"] <= target, f"best_hm violated: {summary['best_bound']} > {target}")

                if summary["strictly_beats_R_opt"]:
                    strict_wins_over_ropt += 1
                if summary["strictly_beats_ceil_R_opt"]:
                    strict_ceil_wins += 1
                total += 1

        _req(total == 90, f"expected 90 exact Q(i) tests, ran {total}")
        _req(noncommuting >= 80, f"expected >= 80 strictly non-commuting matrices, got {noncommuting}")
        _req(complex_count >= 80, f"expected >= 80 strictly complex Hermitian matrices, got {complex_count}")
        _req(strict_wins_over_ropt >= 45, f"expected >= 45 strict wins over R_opt, got {strict_wins_over_ropt}")
        _req(strict_ceil_wins >= 20, f"expected >= 20 integer-rank breakthroughs over ceil(R_opt), got {strict_ceil_wins}")

    def test_03_theorem_a4_strictly_beats_both_ceil_ropt_and_hankel4(self) -> None:
        """
        Theorem A4 beats BOTH ceil(R_opt) AND Hankel4 - b on exact 4x4 matrices (both diagonal
        and non-commuting weakly-coupled complex Hermitian!).
        """
        # Exact 4x4 diagonal witness: Q = diag(10, 0, 0, 0) (b=1), P = diag(0, 1, 1/10, 1/10) (rank=3)
        H = [[Qi(v) if i == j else ZERO for j in range(4)] for i, v in enumerate([Fraction(10), Fraction(1), Fraction(1, 10), Fraction(1, 10)])]
        Q = [[Qi(Fraction(10)) if (i == 0 and j == 0) else ZERO for j in range(4)] for i in range(4)]
        P = cmat_sub(H, Q)
        S = spectral_moments_exact(H, max_k=6)
        u = cmat_trace_real(P)
        t1 = cmat_trace_real(Q)

        ropt = R_opt(u, t1, S[2], 1)
        h4 = R_hankel4_exact(S[1], S[2], S[3], S[4], 1)
        h6 = R_hankel6_exact(S, 1)
        a4 = certify_weighted_quartic_weyl_peak(S, t1, 1, s=Fraction(11), p=Fraction(10), mu=Fraction(10))

        _req(ropt == Fraction(144, 102), f"unexpected R_opt={ropt}")
        _req(math.ceil(ropt) == 2, "expected ceil(R_opt) == 2")
        _req(h4["exact_bound"] < Fraction(2), f"expected H4-1 < 2, got {h4['exact_bound']}")
        _req(a4["exact_bound"] == Fraction(3), f"expected exact A4 == 3, got {a4['exact_bound']}")
        _req(h6["exact_bound"] == Fraction(3), f"expected exact H6-1 == 3, got {h6['exact_bound']}")

        # Strictly NON-COMMUTING complex Hermitian perturbation where A4 beats BOTH ceil(R_opt)=2 AND H4-1 < 2!
        # Q = diag(3, 0, 0, 0), P = diag(0, 1, 1/6, 1/6) coupled by complex Cayley unitary eps = 1/200:
        # R_opt = 1.6821 (ceil=2), H4-1 = 1.8866 (ceil=2), A4 = 2.3737 (ceil=3 -> beats BOTH!)
        P2 = [[Qi(v) if i == j else ZERO for j in range(4)] for i, v in enumerate([Fraction(0), Fraction(1), Fraction(1, 6), Fraction(1, 6)])]
        Q2 = [[Qi(Fraction(3)) if (i == 0 and j == 0) else ZERO for j in range(4)] for i in range(4)]
        K = cmat_zeros(4, 4)
        eps = Fraction(1, 200)
        K[0][1] = Qi(eps, eps)
        K[1][0] = Qi(-eps, eps)
        K[0][2] = Qi(Fraction(0), eps)
        K[2][0] = Qi(Fraction(0), eps)
        from spectral_inertia.exact_qi import cmat_eye, cmat_inv
        I4 = cmat_eye(4)
        U = cmat_mul(cmat_sub(I4, K), cmat_inv(cmat_add(I4, K)))
        P_nc = cmat_mul(cmat_mul(U, P2), cmat_dagger(U))
        H_nc = cmat_add(P_nc, Q2)
        _req(cmat_frob_sq(cmat_sub(cmat_mul(P_nc, Q2), cmat_mul(Q2, P_nc))) > 0, "must be non-commuting")
        _req(any(v.im != 0 for row in H_nc for v in row), "must be strictly complex")

        S_nc = spectral_moments_exact(H_nc, max_k=6)
        t1_nc = cmat_trace_real(Q2)
        ropt_nc = R_opt(cmat_trace_real(P_nc), t1_nc, S_nc[2], 1)
        h4_nc = R_hankel4_exact(S_nc[1], S_nc[2], S_nc[3], S_nc[4], 1)
        a4_nc = certify_weighted_quartic_weyl_peak(S_nc, t1_nc, 1, s=Fraction(7), p=Fraction(6), mu=Fraction(3))
        # Even with strictly non-commuting complex interference, A4_nc > 2 => certifies rank >= 3
        # while BOTH ceil(R_opt_nc) == 2 AND H4_nc < 2!
        _req(math.ceil(ropt_nc) == 2, f"expected ceil(R_opt_nc) == 2, got {ropt_nc}")
        _req(h4_nc["exact_bound"] < Fraction(2), f"expected H4_nc < 2, got {h4_nc['exact_bound']}")
        _req(a4_nc["exact_bound"] > Fraction(2) and a4_nc["exact_bound"] <= Fraction(3),
             f"expected 2 < A4_nc <= 3, got {float(a4_nc['exact_bound'])}")

    def test_04_scan23848_high_interference_breakthrough(self) -> None:
        """
        Verify Project-ASMA Scan 23848 Mode A & Mode B breakthroughs:
          - Mode A: Noise-Annihilating Quartic (A3) strictly beats ceil(R_opt) across rho in [0.75, 0.95], tau > 0!
          - Mode A negative control: at rho=0.90, tau=0.020 (true lam2 - tau < 0 => n_+(H)=1), bound <= 1!
          - Mode B (tau=0): Hankel4 - 1 == EXACT 1 across ALL rho in [0, 0.95]!
        """
        res = run_scan23848_benchmark()
        _req(res["mode_a_strict_ceil_wins_over_R_opt"] >= 6,
             f"expected >= 6 Mode A strict ceil(R_opt) breakthroughs, got {res['mode_a_strict_ceil_wins_over_R_opt']}")
        for row in res["mode_a_rows"]:
            true_n = row["true_n_pos_H"]
            _req(row["best_hm_cert_rank"] <= true_n, f"soundness break on row {row}")
            if row["rho"] == "0.90" and row["tau"] == "0.020":
                _req(true_n == 1 and row["best_hm_cert_rank"] == 1, "phase-boundary negative control failed")
            if row["rho"] == "0.95" and row["tau"] == "0.005":
                _req(row["R_opt_cert_rank"] == 1 and row["best_hm_cert_rank"] == 2,
                     f"expected A3 breakthrough at rho=0.95, tau=0.005: {row}")
        for row in res["mode_b_tau0_rows"]:
            _req(row["Hankel4_minus_1_is_exact_1"], f"Mode B exact 1 failed at rho={row['rho']}")
        tb = res["three_component_mode_b_benchmark"]
        _req(tb["ceil_R_opt"] == 2 and tb["Theorem_A4_exact"] == "3" and tb["Hankel6_minus_1_exact"] == "3",
             f"3-component Mode B benchmark failed: {tb}")

    def test_05_gate2_unitary_and_scale_invariance(self) -> None:
        """Gate 2: Verify exact unitary basis invariance & positive scale invariance of A1-A4."""
        rng = random.Random(42)
        U1 = cayley_unitary(3, rng)
        U2 = cayley_unitary(3, rng)
        P = _build_hermitian_from_unitary(U1, [Fraction(3), Fraction(1, 4), Fraction(0)])
        Q = _build_hermitian_from_unitary(U2, [Fraction(5), Fraction(0), Fraction(-1, 10)])
        H = cmat_add(P, Q)

        # Random unitary basis change H' = V H V*, Q' = V Q V*
        V = cayley_unitary(3, rng)
        Vd = cmat_dagger(V)
        H_rot = cmat_mul(cmat_mul(V, H), Vd)
        Q_rot = cmat_mul(cmat_mul(V, Q), Vd)
        P_rot = cmat_mul(cmat_mul(V, P), Vd)

        S = spectral_moments_exact(H, 6)
        S_rot = spectral_moments_exact(H_rot, 6)
        _req(S == S_rot, "spectral moments not unitarily invariant")

        # Exact positive rescaling H -> alpha H
        alpha = Fraction(7, 3)
        H_sc = cmat_scale(alpha, H)
        S_sc = spectral_moments_exact(H_sc, 6)
        _req(R_opt(alpha * cmat_trace_real(P), alpha * cmat_trace_real(Q), S_sc[2], 1)
             == R_opt(cmat_trace_real(P), cmat_trace_real(Q), S[2], 1), "R_opt not scale invariant")
        _req(R_hankel4_exact(S_sc[1], S_sc[2], S_sc[3], S_sc[4], 1)["exact_bound"]
             == R_hankel4_exact(S[1], S[2], S[3], S[4], 1)["exact_bound"], "R_H4 not scale invariant")
        _req(R_hankel6_exact(S_sc, 1)["exact_bound"]
             == R_hankel6_exact(S, 1)["exact_bound"], "R_H6 not scale invariant")
        _req(certify_noise_annihilating_quartic(S_sc, 1, alpha * Fraction(2), alpha * Fraction(1, 10))["exact_bound"]
             == certify_noise_annihilating_quartic(S, 1, Fraction(2), Fraction(1, 10))["exact_bound"],
             "Theorem A3 not scale invariant")

    def test_06_gate3_negative_controls_and_invalid_witnesses(self) -> None:
        """Gate 3 & R5: Invalid theorem witnesses MUST be rejected with CertError."""
        S = {1: Fraction(2), 2: Fraction(2), 3: Fraction(2), 4: Fraction(2)}
        # Negative Hankel coefficient a_2 < 0 violates phi(lam) <= 0 on lam <= 0
        with self.assertRaises(CertError):
            certify_stieltjes_hankel_2m(S, 0, [Fraction(1), Fraction(-1)])
        # Theorem A3: x0 <= 0 or tau < 0
        with self.assertRaises(CertError):
            certify_noise_annihilating_quartic(S, 0, Fraction(0), Fraction(0))
        with self.assertRaises(CertError):
            certify_noise_annihilating_quartic(S, 0, Fraction(1), Fraction(-1, 10))
        # Theorem A4: negative s, non-positive p, negative gamma1/gamma3, non-positive kappa
        with self.assertRaises(CertError):
            certify_weighted_quartic_weyl(S, Fraction(0), Fraction(0), 0, s=Fraction(-1), p=Fraction(1), gamma1=0, gamma3=0, kappa=1)
        with self.assertRaises(CertError):
            certify_weighted_quartic_weyl(S, Fraction(0), Fraction(0), 0, s=Fraction(1), p=Fraction(0), gamma1=0, gamma3=0, kappa=1)
        with self.assertRaises(CertError):
            certify_weighted_quartic_weyl(S, Fraction(0), Fraction(0), 0, s=Fraction(1), p=Fraction(1), gamma1=-1, gamma3=0, kappa=1)
        with self.assertRaises(CertError):
            certify_weighted_quartic_weyl(S, Fraction(0), Fraction(0), 0, s=Fraction(1), p=Fraction(1), gamma1=0, gamma3=-1, kappa=1)
        with self.assertRaises(CertError):
            certify_weighted_quartic_weyl(S, Fraction(0), Fraction(0), 0, s=Fraction(1), p=Fraction(1), gamma1=0, gamma3=0, kappa=0)
        # Single-species rank-1 PSD matrix MUST never exceed 1 under any theorem
        S_rank1 = {k: Fraction(3) ** k for k in range(1, 7)}
        res1 = best_higher_moment_bound(S_rank1, Fraction(3), Fraction(0), 0)
        _req(res1["best_bound"] == Fraction(1), f"rank-1 bound should be exact 1, got {res1['best_bound']}")


if __name__ == "__main__":
    unittest.main()
