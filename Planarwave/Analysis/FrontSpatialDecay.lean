/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierIdentification

/-!
# All-time spatial semigroup remainder estimate

As in the final paragraph of the paper's semigroup decomposition proof,
combine the identified long-time `C/t` bound with the independently constructed
spatial semigroup's short-time bound. This includes time zero and gives the
`C/(1+t)` estimate in the original supremum norm, expressed via isometric slices.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n d : ℕ}

local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

omit [Nontrivial (ℝ^n)] in
/-- Heat contraction controls the critical term by the fixed profile projection. -/
theorem norm_frontCriticalHeatEvolution_le (t : NNReal) (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) :
    ‖frontCriticalHeatEvolution f D c φ ψ h₃ t v‖ ≤
      ‖profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)‖ * ‖v‖ :=
  (norm_heatFlowBUC_le _ _ _).trans (BUC.norm_postcompCLM_apply_le _ _)

/-- The all-time remainder estimate of the paper's semigroup decomposition
theorem, including zero, for the independently defined spatial evolution. -/
theorem exists_frontSpatialC0Semigroup_remainder_bound (hd : 2 ≤ d) :
    ∃ C > 0, ∀ (t : NNReal) (v : BUC (ℝ^d) (ℂ^n)),
      ‖spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) -
        frontCriticalHeatEvolution f D c φ ψ h₃ t (spatialSlices hd v)‖ ≤
          (C / (1 + t)) * ‖v‖ := by
  obtain ⟨Cl, hCl, hlong⟩ := exists_frontSpatialC0Semigroup_heat_difference_bound f D c φ h₁ h₂ ψ h₃ hd
  obtain ⟨Cs, hCs, hshort⟩ := exists_frontSpatialC0Semigroup_shortTime_bound f D c φ h₁ h₂ hd
  let P := profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  let C : ℝ := 2 * (Cs + ‖P‖ + Cl)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun t v ↦ ?_⟩
  have hden : 0 < 1 + (t : ℝ) := by positivity
  have hheat : ‖frontCriticalHeatEvolution f D c φ ψ h₃ t (spatialSlices hd v)‖ ≤ ‖P‖ * ‖v‖ := by
    simpa only [norm_spatialSlices] using! norm_frontCriticalHeatEvolution_le f D c φ ψ h₃ t (spatialSlices hd v)
  by_cases ht : t ≤ 1
  · have ht' : (t : ℝ) ≤ 1 := ht
    have hfrac : Cs + ‖P‖ ≤ C / (1 + (t : ℝ)) := by
      apply (le_div_iff₀ hden).mpr
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_left ht' (show 0 ≤ Cs + ‖P‖ by positivity)]
    calc
      _ ≤ ‖spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v)‖ +
          ‖frontCriticalHeatEvolution f D c φ ψ h₃ t (spatialSlices hd v)‖ := norm_sub_le _ _
      _ ≤ Cs * ‖v‖ + ‖P‖ * ‖v‖ := by
        rw [norm_spatialSlices]
        exact add_le_add (((frontSpatialC0Semigroup f D c φ h₁ h₂ hd t).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hshort t ht) (norm_nonneg v))) hheat
      _ = (Cs + ‖P‖) * ‖v‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac (norm_nonneg v)
  · have ht' : 1 ≤ (t : ℝ) := (lt_of_not_ge ht).le
    have hpos : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht'
    have hCtwo : 2 * Cl ≤ C := by dsimp [C]; nlinarith [norm_nonneg P]
    have hfrac : Cl / (t : ℝ) ≤ C / (1 + t) := by
      apply (div_le_div_iff₀ hpos hden).mpr
      nlinarith [mul_le_mul_of_nonneg_right hCtwo hpos.le]
    exact (hlong t (show 1 ≤ t from ht') v).trans (mul_le_mul_of_nonneg_right hfrac (norm_nonneg v))

end

end Planarwave
