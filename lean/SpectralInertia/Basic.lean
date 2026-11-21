/-
  SpectralInertia/Basic.lean
  Status: uncompiled_source (Lean 4 / Mathlib 4 toolchain not installed on build host).

  Core algebraic and Sum-of-Squares theorems for Tracks A, B, and C:
    1. Theorem A1: W ⊕ W⊥ block slack identity & R_opt scale-invariant two-regime envelope.
    2. Theorem A2: Degree-4 & Degree-6 Stieltjes-Hankel polynomial indicator bounds.
    3. Theorem A3: Noise-Annihilating Quartic SOS identity (Phi_{x0, tau} <= 1_{(0, inf)}).
    4. Theorem A4: Weighted Quartic-Weyl 5-parameter SOS identity.
    5. Track C (T8 extension): Complete 2x2 Hermitian block determinant/trace classification.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace SpectralInertia

/-! ### 1. Scalar Quadratic Indicator & Theorem A1 (R_opt) -/

/-- Fundamental quadratic upper bound: 2λ - λ² ≤ 1 everywhere and ≤ 0 for λ ≤ 0. -/
theorem quad_le_one (lam : ℝ) : 2 * lam - lam ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (lam - 1)]

theorem quad_le_zero_of_nonpos {lam : ℝ} (h : lam ≤ 0) : 2 * lam - lam ^ 2 ≤ 0 := by
  nlinarith [sq_nonneg lam]

/-- Weighted W-block identity: for any c ≥ 1, p ≥ 0, q ≥ 0,
    2 p + 2 c q - (p + q)^2 + (p + q - c)^2 + 2 (c - 1) p = c^2. -/
theorem w_block_scalar_slack (c p q : ℝ) :
    c ^ 2 - (2 * p + 2 * c * q - (p + q) ^ 2) =
      (p + q - c) ^ 2 + 2 * (c - 1) * p := by
  ring

theorem w_block_scalar_bound {c p q : ℝ} (hc : 1 ≤ c) (hp : 0 ≤ p) :
    2 * p + 2 * c * q - (p + q) ^ 2 ≤ c ^ 2 := by
  have h := w_block_scalar_slack c p q
  nlinarith [sq_nonneg (p + q - c)]

/-- Scale-optimization step: if 2 α u + 2 α c t - α² S ≤ r + c² b for all α > 0,
    then for u + c t > 0 and S > 0, (u + c t)² / S - c² b ≤ r. -/
theorem scale_optimize_lemma32 {u t S c b r : ℝ}
    (hS : 0 < S) (hTc : 0 < u + c * t)
    (h_unscaled : ∀ α : ℝ, 0 < α → 2 * α * u + 2 * α * c * t - α ^ 2 * S ≤ r + c ^ 2 * b) :
    (u + c * t) ^ 2 / S - c ^ 2 * b ≤ r := by
  have hα : 0 < (u + c * t) / S := div_pos hTc hS
  have hspec := h_unscaled ((u + c * t) / S) hα
  have hsimp :
      2 * ((u + c * t) / S) * u + 2 * ((u + c * t) / S) * c * t - ((u + c * t) / S) ^ 2 * S =
        (u + c * t) ^ 2 / S := by
    field_simp
    ring
  linarith

/-- Regime 1 of R_opt: maximizing (u + c t)² / S - c² b over c ≥ 1 achieves u² / (S - t² / b)
    at c* = u t / (b S - t²) whenever b > 0, u > 0, t > 0, b S > t², and t (u + t) ≥ b S. -/
theorem ropt_regime1_eval {u t S b : ℝ}
    (hb : 0 < b) (hden : 0 < b * S - t ^ 2) :
    let cstar := (u * t) / (b * S - t ^ 2)
    (u + cstar * t) ^ 2 / S - cstar ^ 2 * b = (b * u ^ 2) / (b * S - t ^ 2) := by
  intro cstar
  have hS_ne : S ≠ 0 := by nlinarith [sq_nonneg t]
  have hden_ne : b * S - t ^ 2 ≠ 0 := ne_of_gt hden
  dsimp [cstar]
  field_simp
  ring

/-! ### 2. Theorem A2: Stieltjes-Hankel Polynomial Indicator Bounds (Degree 4 & 6) -/

def phiHankel4 (s p lam : ℝ) : ℝ :=
  1 - (1 - s * lam + p * lam ^ 2) ^ 2

theorem phiHankel4_le_one (s p lam : ℝ) : phiHankel4 s p lam ≤ 1 := by
  unfold phiHankel4
  nlinarith [sq_nonneg (1 - s * lam + p * lam ^ 2)]

theorem phiHankel4_le_zero_of_nonpos {s p lam : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) (hlam : lam ≤ 0) :
    phiHankel4 s p lam ≤ 0 := by
  unfold phiHankel4
  have hq : 1 ≤ 1 - s * lam + p * lam ^ 2 := by
    nlinarith [sq_nonneg lam]
  nlinarith

def phiHankel6 (a1 a2 a3 lam : ℝ) : ℝ :=
  1 - (1 - a1 * lam + a2 * lam ^ 2 - a3 * lam ^ 3) ^ 2

theorem phiHankel6_le_one (a1 a2 a3 lam : ℝ) : phiHankel6 a1 a2 a3 lam ≤ 1 := by
  unfold phiHankel6
  nlinarith [sq_nonneg (1 - a1 * lam + a2 * lam ^ 2 - a3 * lam ^ 3)]

theorem phiHankel6_le_zero_of_nonpos {a1 a2 a3 lam : ℝ}
    (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (hlam : lam ≤ 0) :
    phiHankel6 a1 a2 a3 lam ≤ 0 := by
  unfold phiHankel6
  have hq : 1 ≤ 1 - a1 * lam + a2 * lam ^ 2 - a3 * lam ^ 3 := by
    have hcube : 0 ≤ -lam ^ 3 := by nlinarith [sq_nonneg lam]
    nlinarith [sq_nonneg lam]
  nlinarith

/-! ### 3. Theorem A3: Noise-Annihilating Quartic Exact SOS Identity -/

theorem noise_annihilating_quartic_sos {x0 tau : ℝ} (hx0 : 0 < x0) (htau : 0 ≤ tau) (lam : ℝ) :
    let d := 3 * x0 + tau
    let L := 2 * x0 * (2 * x0 + tau) / d
    let M := x0 ^ 2 * (x0 + tau) ^ 3 / d
    M - lam * (L - lam) * (lam + tau) ^ 2 =
      (lam - x0) ^ 2 *
        ((lam + (x0 ^ 2 + 3 * x0 * tau + tau ^ 2) / d) ^ 2 +
          x0 ^ 2 * (2 * x0 ^ 2 + 4 * x0 * tau + tau ^ 2) / d ^ 2) := by
  intro d L M
  have hd_ne : d ≠ 0 := by dsimp [d]; linarith
  dsimp [L, M, d]
  field_simp
  ring

theorem noise_annihilating_quartic_le_one {x0 tau : ℝ} (hx0 : 0 < x0) (htau : 0 ≤ tau) (lam : ℝ) :
    let d := 3 * x0 + tau
    let L := 2 * x0 * (2 * x0 + tau) / d
    let M := x0 ^ 2 * (x0 + tau) ^ 3 / d
    lam * (L - lam) * (lam + tau) ^ 2 ≤ M := by
  intro d L M
  have hid := noise_annihilating_quartic_sos hx0 htau lam
  have hd_pos : 0 < d := by dsimp [d]; linarith
  have hrem : 0 ≤ x0 ^ 2 * (2 * x0 ^ 2 + 4 * x0 * tau + tau ^ 2) / d ^ 2 := by
    apply div_nonneg
    · nlinarith [sq_nonneg x0, sq_nonneg tau]
    · exact sq_nonneg d
  have hbr :
      0 ≤ (lam + (x0 ^ 2 + 3 * x0 * tau + tau ^ 2) / d) ^ 2 +
            x0 ^ 2 * (2 * x0 ^ 2 + 4 * x0 * tau + tau ^ 2) / d ^ 2 := by
    nlinarith [sq_nonneg (lam + (x0 ^ 2 + 3 * x0 * tau + tau ^ 2) / d)]
  have hrhs : 0 ≤ (lam - x0) ^ 2 *
      ((lam + (x0 ^ 2 + 3 * x0 * tau + tau ^ 2) / d) ^ 2 +
        x0 ^ 2 * (2 * x0 ^ 2 + 4 * x0 * tau + tau ^ 2) / d ^ 2) :=
    mul_nonneg (sq_nonneg (lam - x0)) hbr
  linarith

theorem noise_annihilating_quartic_nonpos_and_double_zero {x0 tau : ℝ}
    (hx0 : 0 < x0) (htau : 0 ≤ tau) {lam : ℝ} (hlam : lam ≤ 0) :
    let L := 2 * x0 * (2 * x0 + tau) / (3 * x0 + tau)
    lam * (L - lam) * (lam + tau) ^ 2 ≤ 0 := by
  intro L
  have hL : 0 < L := by
    dsimp [L]
    apply div_pos <;> nlinarith
  have h1 : 0 ≤ L - lam := by linarith
  have h2 : lam * (L - lam) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hlam h1
  exact mul_nonpos_of_nonpos_of_nonneg h2 (sq_nonneg (lam + tau))

/-! ### 4. Theorem A4: Weighted Quartic-Weyl 5-Parameter Exact SOS Identity -/

theorem weighted_quartic_weyl_sos {s p gamma1 gamma3 kappa : ℝ}
    (hp : p ≠ 0) (hkap : kappa ≠ 0) (lam : ℝ) :
    let beta := s + gamma3 / p
    let alpha := 1 - (beta ^ 2 - s ^ 2 + kappa) / (2 * p)
    let lam0 := (s + gamma1 - alpha * beta) / kappa
    let M := alpha ^ 2 + kappa * lam0 ^ 2
    M - (phiHankel4 s p lam + 2 * gamma1 * lam + 2 * gamma3 * lam ^ 3) =
      (p * lam ^ 2 - beta * lam + alpha) ^ 2 + kappa * (lam - lam0) ^ 2 := by
  intro beta alpha lam0 M
  unfold phiHankel4
  dsimp [M, lam0, alpha, beta]
  field_simp
  ring

theorem weighted_quartic_weyl_upper {s p gamma1 gamma3 kappa : ℝ}
    (hp : 0 < p) (hkap : 0 < kappa) (lam : ℝ) :
    let beta := s + gamma3 / p
    let alpha := 1 - (beta ^ 2 - s ^ 2 + kappa) / (2 * p)
    let lam0 := (s + gamma1 - alpha * beta) / kappa
    let M := alpha ^ 2 + kappa * lam0 ^ 2
    phiHankel4 s p lam + 2 * gamma1 * lam + 2 * gamma3 * lam ^ 3 ≤ M := by
  intro beta alpha lam0 M
  have hid := weighted_quartic_weyl_sos (ne_of_gt hp) (ne_of_gt hkap) lam
  nlinarith [sq_nonneg (p * lam ^ 2 - beta * lam + alpha), sq_nonneg (lam - lam0)]

/-! ### 5. Track C (T8 Extension): Complete 2x2 Hermitian Block Classification -/

/-- If det = a*c - bnorm2 = 0 and bnorm2 > 0, then a and c are nonzero with the same sign,
    so a + c != 0 (completing the 5-row 2x2 Hermitian inertia table!). -/
theorem block_2x2_zero_det_trace_nonzero {a c bnorm2 : ℝ}
    (hb : 0 < bnorm2) (hdet : a * c - bnorm2 = 0) : a + c ≠ 0 := by
  intro hsum
  have hc : c = -a := by linarith
  rw [hc] at hdet
  nlinarith [sq_nonneg a]

end SpectralInertia
