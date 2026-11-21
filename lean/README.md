# Lean 4 Formalization Status (`SpectralInertia`)

## Toolchain Check (Honest Audit)
Checked host environment on `2026-11-20`:
- `which lean` -> not installed
- `which lake` -> not installed
- `which elan` -> not installed (`~/.elan/bin` absent)

**Provenance / Status:** `uncompiled_source` (NOT kernel-verified locally because `lean`/`lake` is not present on this machine). No kernel-check claim is made until compiled under Lean 4 + Mathlib 4.

## What `SpectralInertia/Basic.lean` Formalizes
1. `ropt_block_slack_identity`: The exact $W \oplus W^\perp$ algebraic slack identity underlying Theorem A1 (`R_opt` and non-commuting generalized Lemma 3.2) for any $c \ge 1$.
2. `ropt_regime1_and_regime2`: Algebraic derivation of the scale-invariant two-regime envelope $R_{\mathrm{opt}}(u, t, S, b)$ (including strict positivity of $S - t^2/b$ when $u > 0, t > 0, b > 0$).
3. `stieltjes_hankel_poly_bounds` (Theorem A2): Proof that $\phi_a(\lambda) = 1 - (1 + \sum_{k=1}^m (-1)^k a_k \lambda^k)^2 \le \mathbf{1}_{\lambda > 0}$ for all $\lambda \in \mathbb{R}$ whenever every $a_k \ge 0$ (explicitly proved for $m = 2, 3$).
4. `noise_annihilating_quartic_sos` (Theorem A3): Exact closed-form Sum-of-Squares identity proving $1 - \Phi_{x_0,\tau}(\lambda) \ge 0$ for all $\lambda \in \mathbb{R}$, $\Phi_{x_0,\tau}(\lambda) \le 0$ for all $\lambda \le 0$, and double zero $\Phi_{x_0,\tau}(-\tau) = 0$.
5. `weighted_quartic_weyl_sos` (Theorem A4): Exact closed-form 5-parameter Sum-of-Squares identity proving $M - (\phi_{s,p}(\lambda) + 2\gamma_1\lambda + 2\gamma_3\lambda^3) = (p\lambda^2 - \beta\lambda + \alpha)^2 + \kappa(\lambda - \lambda_0)^2 \ge 0$ for all $\lambda \in \mathbb{R}$.
6. `sylvester_2x2_block_inertia`: Exhaustive algebraic classification of $2 \times 2$ Hermitian blocks (`det < 0`, `det > 0 & tr > 0`, `det > 0 & tr < 0`, `det = 0 & b != 0`) extending `T8`.
