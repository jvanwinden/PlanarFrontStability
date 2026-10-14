/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontLinearizedSemigroup
import all Planarwave.Analysis.ComplexFrequencySemigroupBounds

/-!
# All-frequency longitudinal semigroup bounds

Following the second bounded perturbation in Lemma 2.2, the contour-shift operator is added to
the real-frequency semigroup. The generator is exactly the complex-frequency pencil on the
same `ComplexBUC2` domain. Young's inequality absorbs half the real-frequency damping and
gives constants independent of both real and imaginary frequency.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- The longitudinal semigroup at the shifted contour frequency `ξ₀ + i ξ₁`. -/
def frontComplexFrequencyC0Semigroup (ξ₀ ξ₁ : ℝ^m) : C0Semigroup ℂ (BUC ℝ (ℂ^n)) :=
  (frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ₀‖ ^ 2)).boundedPerturbation
    (frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁)

/-- The second bounded perturbation has precisely the complex-frequency pencil as generator. -/
theorem frontComplexFrequencyC0Semigroup_hasGeneratorAt_iff (ξ₀ ξ₁ : ℝ^m)
    (x y : BUC ℝ (ℂ^n)) :
    (frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁).HasGeneratorAt x y ↔
      ∃ v : ComplexBUC2 (ℂ^n), ComplexBUC2.value (ℂ^n) v = x ∧
        frontLongitudinalPencil f D c φ h₁ h₂
          (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)) v = y := by
  rw [frontComplexFrequencyC0Semigroup, C0Semigroup.boundedPerturbation_hasGeneratorAt_iff,
    frontLinearizedC0Semigroup_hasGeneratorAt_iff]
  apply exists_congr
  intro v
  have hshift : frontLongitudinalPencil f D c φ h₁ h₂
        (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)) v =
      frontLongitudinalPencil f D c φ h₁ h₂ ((‖ξ₀‖ ^ 2 : ℝ) : ℂ) v +
        frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁ (ComplexBUC2.value (ℂ^n) v) := by
    have h := congrArg (fun L : ComplexBUC2 (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) ↦ L v)
      (frontLongitudinalPencil_shift_sub_real_eq f D c φ h₁ h₂ ξ₀ ξ₁)
    change _ - _ = frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁
      (ComplexBUC2.value (ℂ^n) v) at h
    rw [sub_eq_iff_eq_add] at h
    simpa only [add_comm] using! h
  constructor
  · rintro ⟨hv, hy⟩
    exact ⟨hv, by rw [hshift, hv, hy, sub_add_cancel]⟩
  · rintro ⟨hv, hy⟩
    rw [hshift, hv] at hy
    exact ⟨hv, eq_sub_iff_add_eq.mpr hy⟩

/-- The operator-semigroup half of Lemma 2.2, with constants uniform in all frequencies. -/
theorem exists_frontComplexFrequency_allFrequency_bound :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal),
      ‖frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t‖ ≤
        M * Real.exp (κ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ, hμ, C, hC, hbound⟩ := exists_uniform_frontLinearized_bound f D c φ h₁ h₂
  let K := M * ‖frontComplexifiedDiffusionBUC D‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ := μ / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (2 * (K + 1)) = μ := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hδsmall : K * δ ≤ μ / 2 := by nlinarith
  let κ := C + K * (1 + δ⁻¹) + 1
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hCκ : C ≤ κ := by
    have hkδ : 0 ≤ K * (1 + δ⁻¹) := by positivity
    dsimp [κ]
    linarith
  have hKκ : K * (1 + δ⁻¹) ≤ κ := by dsimp [κ]; linarith
  refine ⟨M, hM, μ / 2, by positivity, κ, hκ, ?_⟩
  intro ξ₀ ξ₁ t
  let B := frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁
  have hpert : M * ‖B‖ ≤ K * δ * ‖ξ₀‖ ^ 2 + K * (1 + δ⁻¹) * ‖ξ₁‖ ^ 2 := by
    calc
      M * ‖B‖ ≤ M * ((δ * ‖ξ₀‖ ^ 2 + (1 + δ⁻¹) * ‖ξ₁‖ ^ 2) *
          ‖frontComplexifiedDiffusionBUC D‖) :=
        mul_le_mul_of_nonneg_left
          (norm_frontComplexFrequencyBoundedPerturbation_le_young D ξ₀ ξ₁ hδ) hM.le
      _ = _ := by dsimp [K]; ring
  have hrate : C - μ * ‖ξ₀‖ ^ 2 + M * ‖B‖ ≤
      κ - μ / 2 * ‖ξ₀‖ ^ 2 + κ * ‖ξ₁‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδsmall) (sq_nonneg ‖ξ₀‖),
      mul_nonneg (sub_nonneg.mpr hKκ) (sq_nonneg ‖ξ₁‖)]
  have hfree : ∀ r : NNReal,
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ₀‖ ^ 2) r‖ ≤
        M * Real.exp ((C - μ * ‖ξ₀‖ ^ 2) * r) := by
    intro r
    simpa only [sub_mul] using hbound (‖ξ₀‖ ^ 2) (sq_nonneg _) r
  have h := (frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ₀‖ ^ 2)).norm_boundedPerturbation_le
    B hM.le hfree t
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  simpa only [add_mul, sub_mul] using! mul_le_mul_of_nonneg_right hrate t.2

/-- Lemma 2.2: the longitudinal semigroup and scalar heat multiplier obey one common estimate. -/
theorem exists_front_allFrequency_bound (ψ : ℝ → ℝ^n)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal),
      ‖frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t‖ +
        ‖Complex.exp (-(t * d_perp D φ ψ : ℂ) *
          complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ ≤
        M * Real.exp (κ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ₁, hμ₁, κ₁, hκ₁, hS⟩ :=
    exists_frontComplexFrequency_allFrequency_bound (m := m) f D c φ h₁ h₂
  obtain ⟨μ₂, hμ₂, κ₂, hκ₂, hH⟩ :=
    exists_frontHeatMultiplier_allFrequency_bound (m := m) f D c φ ψ h₃
  let μ := min μ₁ μ₂
  let κ := max κ₁ κ₂
  have hμ : 0 < μ := lt_min hμ₁ hμ₂
  have hκ : 0 < κ := hκ₁.trans_le (le_max_left _ _)
  refine ⟨M + 1, by positivity, μ, hμ, κ, hκ, ?_⟩
  intro ξ₀ ξ₁ t
  have hrate {a b : ℝ} (ha : a ≤ κ) (hb : μ ≤ b) :
      a * (t : ℝ) - b * ‖ξ₀‖ ^ 2 * t + a * ‖ξ₁‖ ^ 2 * t ≤
        κ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t := by
    gcongr
  have hS' := (hS ξ₀ ξ₁ t).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (hrate (le_max_left _ _) (min_le_left _ _))) hM.le)
  have hH' := (hH (t : ℝ) ξ₀ ξ₁ t.2).trans
    (Real.exp_le_exp.mpr (hrate (le_max_right _ _) (min_le_right _ _)))
  simpa only [add_mul, one_mul] using add_le_add hS' hH'

end

end Planarwave
