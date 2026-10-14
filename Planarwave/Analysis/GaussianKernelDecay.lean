/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianFourierKernel

@[expose] public section

/-!
# Time powers and small shifts in the on-diagonal kernel estimate

These are the scalar estimates used after integrating the three frequency
contributions: exponential decay absorbs every time power, the frequency
Gaussian contributes `t⁻ᵐᐟ²`, and the small contour offset retains half of its
spatial Gaussian after allowing for imaginary-frequency growth.
-/

open scoped InnerProductSpace

namespace Planarwave

noncomputable section

/-- Exponential decay dominates any prescribed real power, uniformly for `t ≥ 1`. -/
theorem exists_exp_neg_mul_le_rpow {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ∃ C > 0, ∀ t : ℝ, 1 ≤ t → Real.exp (-a * t) ≤ C * t ^ (-p) := by
  obtain ⟨N, hN⟩ := exists_nat_ge p
  let C : ℝ := (N.factorial : ℝ) / a ^ N
  have hf : 0 < (N.factorial : ℝ) := by positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hpoly : t ^ p ≤ t ^ N := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le ht hN
  have hpow : t ^ N ≤ C * Real.exp (a * t) := by
    calc
      t ^ N = ((a * t) ^ N / (N.factorial : ℝ)) * C := by
        dsimp [C]
        rw [mul_pow]
        field_simp
      _ ≤ Real.exp (a * t) * C :=
        mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp (a * t) (by positivity) N) hC.le
      _ = _ := mul_comm _ _
  have hprod : t ^ p * Real.exp (-a * t) ≤ C := by
    calc
      t ^ p * Real.exp (-a * t) ≤ (C * Real.exp (a * t)) * Real.exp (-a * t) := by
        gcongr
        exact hpoly.trans hpow
      _ = C := by rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
  rw [Real.rpow_neg htpos.le]
  change Real.exp (-a * t) ≤ C / t ^ p
  exact (le_div_iff₀ (Real.rpow_pos_of_pos htpos p)).mpr (by simpa only [mul_comm] using hprod)

/-- Exact Gaussian frequency-mass scaling. -/
theorem gaussian_mass_scaling {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (p : ℝ) :
    (Real.pi / (μ * t)) ^ p = (Real.pi / μ) ^ p * t ^ (-p) := by
  rw [div_mul_eq_div_div, Real.div_rpow (by positivity) ht.le, Real.rpow_neg ht.le]
  rfl

/-- Combining the critical Taylor `1/t` with the frequency Gaussian mass. -/
theorem critical_gaussian_mass_scaling {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (M p : ℝ) :
    (M / t) * (Real.pi / (μ * t)) ^ p = M * (Real.pi / μ) ^ p * t ^ (-(p + 1)) := by
  rw [gaussian_mass_scaling hμ ht, show -(p + 1) = -p + (-1) by ring,
    Real.rpow_add ht, Real.rpow_neg_one]
  ring

/-- The Gaussian mass is uniformly bounded for `t ≥ 1`. -/
theorem gaussian_mass_le {μ t p : ℝ} (hμ : 0 < μ) (ht : 1 ≤ t) (hp : 0 ≤ p) :
    (Real.pi / (μ * t)) ^ p ≤ (Real.pi / μ) ^ p := by
  apply Real.rpow_le_rpow (by positivity) _ hp
  apply div_le_div_of_nonneg_left Real.pi_pos.le hμ
  nlinarith

/-- Choose one positive shift satisfying all three smallness requirements from the paper. -/
theorem exists_onDiagonal_small_shift {k R μ₃ κ₃ κ₂ : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hμ₃ : 0 < μ₃) (hκ₃ : 0 < κ₃) (hκ₂ : 0 < κ₂) :
    ∃ ε > 0, ε * R ≤ k ∧ κ₃ * (ε * R) ^ 2 ≤ μ₃ / 2 ∧ κ₂ * ε ≤ 1 / 2 := by
  let δ := min (k / R) (min (Real.sqrt (μ₃ / (2 * κ₃ * R ^ 2))) ((2 * κ₂)⁻¹))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have heδ : ε ≤ δ := by dsimp [ε]; linarith
  have hek : ε ≤ k / R := heδ.trans (min_le_left _ _)
  have hes : ε ≤ Real.sqrt (μ₃ / (2 * κ₃ * R ^ 2)) :=
    heδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heκ : ε ≤ (2 * κ₂)⁻¹ := heδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, (le_div_iff₀ hR).mp hek, ?_, ?_⟩
  · have hs := pow_le_pow_left₀ hε.le hes 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have h := (le_div_iff₀ (by positivity : 0 < 2 * κ₃ * R ^ 2)).mp hs
    nlinarith
  · have h := mul_le_mul_of_nonneg_left heκ hκ₂.le
    have heq : κ₂ * (2 * κ₂)⁻¹ = (1 / 2 : ℝ) := by field_simp
    rwa [heq] at h

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The imaginary offset stays in the low-frequency box in the on-diagonal region. -/
theorem norm_onDiagonal_shift_le {ε t R : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (x : V) (hx : ‖x‖ / t ≤ R) : ‖(ε / t) • x‖ ≤ ε * R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hε ht.le)]
  calc
    (ε / t) * ‖x‖ = ε * (‖x‖ / t) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx hε

/-- The extracted real exponential absorbs the imaginary-frequency growth,
retaining half the spatial Gaussian. -/
theorem onDiagonal_shift_exponent_le {ε κ t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hsmall : κ * ε ≤ 1 / 2) (x : V) :
    -⟪(ε / t) • x, x⟫_ℝ + κ * ‖(ε / t) • x‖ ^ 2 * t ≤ -(ε / 2) * ‖x‖ ^ 2 / t := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hε ht.le)]
  have h := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ ε * ‖x‖ ^ 2 / t by positivity)
  calc
    -(ε / t * ‖x‖ ^ 2) + κ * (ε / t * ‖x‖) ^ 2 * t =
        (κ * ε) * (ε * ‖x‖ ^ 2 / t) - ε * ‖x‖ ^ 2 / t := by field_simp; ring
    _ ≤ (1 / 2) * (ε * ‖x‖ ^ 2 / t) - ε * ‖x‖ ^ 2 / t := sub_le_sub_right h _
    _ = _ := by ring

end

end Planarwave
