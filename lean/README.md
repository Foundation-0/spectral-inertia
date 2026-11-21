# Lean 4 Formalization Status (`SpectralInertia`)

## Compile Status

**Provenance / Status:** `compiled_scalar_identities_only`. Compiled on `2026-11-20` with `lean` 4.35.0 (`eb6cafb7290e`) against Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (tag `v4.35.0`). `lean SpectralInertia/Basic.lean` exits 0 with no warnings or errors. The file has no `sorry`, no `admit` and no added axioms. `#print axioms` on every theorem and def lists only `propext`, `Classical.choice` and `Quot.sound`.

**Scope of the claim:** this covers scalar identities and inequalities over `ℝ` only. None of the matrix statements (the block, Hermitian-inertia or operator-level claims in the paper) is formalized or checked here. A compiled scalar identity says nothing about the matrix statement it is used to support.

The file uses `import Mathlib` because the module that holds `ℝ` has moved between Mathlib versions (`Mathlib.Data.Real.Basic` is now a deprecated alias) and `Mathlib.Tactic.Nlinarith` no longer exists. `nlinarith` is provided by `Mathlib.Tactic.Linarith`.

## What `SpectralInertia/Basic.lean` Formalizes
1. `ropt_block_slack_identity`: The exact $W \oplus W^\perp$ algebraic slack identity underlying Theorem A1 (`R_opt` and non-commuting generalized Lemma 3.2) for any $c \ge 1$.
2. `ropt_regime1_and_regime2`: Algebraic derivation of the scale-invariant two-regime envelope $R_{\mathrm{opt}}(u, t, S, b)$ (including strict positivity of $S - t^2/b$ when $u > 0, t > 0, b > 0$).
3. `stieltjes_hankel_poly_bounds` (Theorem A2): Proof that $\phi_a(\lambda) = 1 - (1 + \sum_{k=1}^m (-1)^k a_k \lambda^k)^2 \le \mathbf{1}_{\lambda > 0}$ for all $\lambda \in \mathbb{R}$ whenever every $a_k \ge 0$ (explicitly proved for $m = 2, 3$).
4. `noise_annihilating_quartic_sos` (Theorem A3): Exact closed-form Sum-of-Squares identity proving $1 - \Phi_{x_0,\tau}(\lambda) \ge 0$ for all $\lambda \in \mathbb{R}$, $\Phi_{x_0,\tau}(\lambda) \le 0$ for all $\lambda \le 0$, and double zero $\Phi_{x_0,\tau}(-\tau) = 0$.
5. `weighted_quartic_weyl_sos` (Theorem A4): Exact closed-form 5-parameter Sum-of-Squares identity proving $M - (\phi_{s,p}(\lambda) + 2\gamma_1\lambda + 2\gamma_3\lambda^3) = (p\lambda^2 - \beta\lambda + \alpha)^2 + \kappa(\lambda - \lambda_0)^2 \ge 0$ for all $\lambda \in \mathbb{R}$.
6. `sylvester_2x2_block_inertia`: Exhaustive algebraic classification of $2 \times 2$ Hermitian blocks (`det < 0`, `det > 0 & tr > 0`, `det > 0 & tr < 0`, `det = 0 & b != 0`) extending `T8`.
