/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierContour

/-!
# Off-diagonal bounds for the spatial remainder kernel

Follow the paper's off-diagonal proposition: choose the contour offset
`η = x / (2 κ t)`, integrate the frequency Gaussian, and split the spatial
exponential using the threshold `4 κ` and rate `min κ (8 κ)⁻¹`.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-- The paper's choice `ε = (2 κ)⁻¹` gives the exact localized exponent. -/
theorem offDiagonal_shift_exponent {m : ℕ} {κ t : ℝ} (hκ : 0 < κ) (ht : 0 < t) (x : ℝ^m) :
    κ * t - ⟪(2 * κ * t)⁻¹ • x, x⟫_ℝ + κ * ‖(2 * κ * t)⁻¹ • x‖ ^ 2 * t =
      κ * t - ‖x‖ ^ 2 / (4 * κ * t) := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2 * κ * t)⁻¹)]
  field_simp
  ring

/-- Split the spatial Gaussian in half and absorb time growth beyond the threshold `4 κ`. -/
theorem offDiagonal_exponent_le {κ t r : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    (hfar : 4 * κ ≤ r / t) :
    κ * t - r ^ 2 / (4 * κ * t) ≤
      -(min κ (8 * κ)⁻¹) * t - (min κ (8 * κ)⁻¹) * r ^ 2 / t := by
  have hrt : 4 * κ * t ≤ r := (le_div_iff₀ ht).mp hfar
  have hrsq : (4 * κ * t) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hrt 2
  have habsorb : 2 * κ * t ≤ r ^ 2 / (8 * κ * t) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have htime : min κ (8 * κ)⁻¹ * t ≤ κ * t :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le
  have hspace : min κ (8 * κ)⁻¹ * r ^ 2 / t ≤ r ^ 2 / (8 * κ * t) := by
    calc
      min κ (8 * κ)⁻¹ * r ^ 2 / t ≤ (8 * κ)⁻¹ * r ^ 2 / t := by
        gcongr
        exact min_le_right _ _
      _ = _ := by field_simp
  have hsplit : r ^ 2 / (4 * κ * t) = 2 * (r ^ 2 / (8 * κ * t)) := by
    field_simp
    ring
  rw [hsplit]
  linarith

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) := by
  exact SeminormedAddGroup.toContinuousENorm (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))

local instance : TopologicalSpace.PseudoMetrizableSpace (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) := by
  exact PseudoEMetricSpace.pseudoMetrizableSpace (α := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))

/-- The optimized contour gives a spatial Gaussian at every positive time.
Its exponentially growing time prefactor is removed in the off-diagonal regime below. -/
theorem exists_frontRemainderKernel_globalGaussian_bound :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (t : NNReal), 0 < t → ∀ x : ℝ^m,
      ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ ≤
        M * (Real.pi / (μ * t)) ^ (m / 2 : ℝ) *
          Real.exp (κ * t - ‖x‖ ^ 2 / (4 * κ * t)) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, hb⟩ :=
    exists_frontShiftedRemainderKernel_gaussian_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨M, hM, μ, hμ, κ, hκ, ?_⟩
  intro t ht x
  have h := hb t ht ((2 * κ * (t : ℝ))⁻¹ • x) x
  rw [frontShiftedRemainderKernel_eq f D c φ h₁ h₂ ψ h₃ t ht] at h
  apply h.trans_eq
  congr 2
  exact offDiagonal_shift_exponent hκ ht x

/-- The outer spatial integral is absolutely convergent in operator norm at every
positive time. This asserts integrability, not the final uniform-in-time remainder bound. -/
theorem integrable_frontRemainderKernel (t : NNReal) (ht : 0 < t) :
    Integrable (frontRemainderKernel (m := m) f D c φ h₁ h₂ ψ h₃ t) := by
  obtain ⟨M, _, μ, _, κ, hκ, hb⟩ :=
    exists_frontRemainderKernel_globalGaussian_bound (m := m) f D c φ h₁ h₂ ψ h₃
  have hbt : 0 < (4 * κ * (t : ℝ))⁻¹ := by positivity
  apply Integrable.mono' (β := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
    ((integrable_gaussian_norm (V := ℝ^m) hbt).const_mul
      (M * (Real.pi / (μ * t)) ^ (m / 2 : ℝ) * Real.exp (κ * t)))
      (Continuous.aestronglyMeasurable (β := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
        (continuous_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht))
  filter_upwards [] with x
  apply (hb t ht x).trans_eq
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The off-diagonal proposition in operator norm, from the original front hypotheses. -/
theorem exists_frontRemainderKernel_offDiagonal_bound :
    ∃ C > 0, ∃ R > 0, ∃ ν > 0, ∀ (t : NNReal), 1 ≤ t → ∀ x : ℝ^m,
      R ≤ ‖x‖ / t →
      ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ ≤
        C * Real.exp (-ν * t - ν * ‖x‖ ^ 2 / t) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, hb⟩ :=
    exists_frontRemainderKernel_globalGaussian_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨M * (Real.pi / μ) ^ (m / 2 : ℝ), by positivity,
    4 * κ, by positivity, min κ (8 * κ)⁻¹, lt_min hκ (by positivity), ?_⟩
  intro t ht x hx
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le (by norm_num) ht
  have hbase : Real.pi / (μ * t) ≤ Real.pi / μ := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le hμ
    nlinarith
  have hmass : (Real.pi / (μ * t)) ^ (m / 2 : ℝ) ≤ (Real.pi / μ) ^ (m / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbase (by positivity)
  apply (hb t htpos x).trans
  apply mul_le_mul (mul_le_mul_of_nonneg_left hmass hM.le)
    (Real.exp_le_exp.mpr (offDiagonal_exponent_le hκ htpos hx))
    (Real.exp_pos _).le (by positivity)

/-- The pointwise form used for longitudinal slices of BUC perturbations. -/
theorem exists_frontRemainderKernel_offDiagonal_pointwise_bound :
    ∃ C > 0, ∃ R > 0, ∃ ν > 0, ∀ (t : NNReal), 1 ≤ t → ∀ x : ℝ^m,
      R ≤ ‖x‖ / t → ∀ (v : BUC ℝ (ℂ^n)) (z : ℝ),
      ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x v z‖ ≤
        C * Real.exp (-ν * t - ν * ‖x‖ ^ 2 / t) * ‖v‖ := by
  obtain ⟨C, hC, R, hR, ν, hν, hb⟩ :=
    exists_frontRemainderKernel_offDiagonal_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨C, hC, R, hR, ν, hν, ?_⟩
  intro t ht x hx v z
  exact (BUC.norm_apply_le _ z).trans
    (((frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb t ht x hx) (norm_nonneg v)))

end

end Planarwave
