/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Definitions
import all Planarwave.Analysis.PhaseFunctional
import all Planarwave.Analysis.ProfileProjection
import all Planarwave.Analysis.TranslationMode
import all Planarwave.Analysis.TransverseOperatorBridge
import Planarwave.Analysis.ClosedOperator
import Planarwave.Analysis.FredholmProjection

/-!
# The concrete horizontal Fredholm splitting

This module instantiates the abstract simple-zero-mode package with the horizontal front operator.
It is the algebraic/Fredholm part of Proposition 2.1 in the paper.  The coefficient family is
supplied as a bundled BUC map with its pointwise identification; its construction from the smooth
front hypotheses is kept separate.
-/

open Function Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
  (c : ℝ) (φ ψ : ℝ → ℝ^n)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
  (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n))
  (hA : ∀ z v, A z v = (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) v)

include hA

/-- The kernel of the concrete horizontal graph-domain operator is exactly the span of the
canonical translation mode. -/
theorem horizontalOperator_kernel_eq_span :
    LinearMap.ker (challengeTransverseOperator D c A 0).toLinearMap =
      Submodule.span ℂ {translationModeComplexBUC2 f D c φ ψ h₃} := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    have hvresEq : challengeResolventMap D c A 0 0 v = 0 := by
      rw [challengeResolventMap_zero]
      exact hv
    have hvres :=
      isTransverseResolventSolution_of_operatorEquation f D c φ A hA hvresEq
    obtain ⟨a, ha⟩ := (h₃.horizontal_kernel (v : ℝ → ℂ^n)).mp hvres
    refine ⟨a, ?_⟩
    apply DFunLike.coe_injective
    funext z
    change a • embed (deriv φ z) = v z
    exact (ha z).symm
  · rintro ⟨a, ha⟩
    have hvres : IsTransverseResolventSolution f D c φ 0 0
        (v : ℝ → ℂ^n) 0 := by
      apply (h₃.horizontal_kernel (v : ℝ → ℂ^n)).mpr
      refine ⟨a, fun z ↦ ?_⟩
      have hz := congrArg (fun q : ComplexBUC2 (ℂ^n) ↦ q z) ha
      calc
        v z = (a • translationModeComplexBUC2 f D c φ ψ h₃) z := hz.symm
        _ = a • translationModeComplexBUC2 f D c φ ψ h₃ z := rfl
        _ = a • embed (deriv φ z) := by
          rw [translationModeComplexBUC2_apply]
    have hvresEq : challengeResolventMap D c A 0 0 v = 0 :=
      operatorEquation_of_isTransverseResolventSolution f D c φ A hA hvres
    rw [challengeResolventMap_zero] at hvresEq
    exact hvresEq

/-- Concrete Fredholm solvability: the range of the horizontal operator is the kernel of the
phase functional. -/
theorem exists_horizontalOperator_eq_iff_phase_zero (w : BUC ℝ (ℂ^n)) :
    (∃ u : ComplexBUC2 (ℂ^n), challengeTransverseOperator D c A 0 u = w) ↔
      phaseFunctional ψ h₃.integrable w = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have hresEq : challengeResolventMap D c A 0 0 u = w := by
      rw [challengeResolventMap_zero]
      exact hu
    have hres := isTransverseResolventSolution_of_operatorEquation f D c φ A hA hresEq
    exact (phaseFunctional_eq_zero_iff_horizontal_solvable h₃ w).mpr ⟨u, hres⟩
  · intro hw
    obtain ⟨v, hv⟩ := (phaseFunctional_eq_zero_iff_horizontal_solvable h₃ w).mp hw
    let u : ComplexBUC2 (ℂ^n) :=
      complexBUC2OfTransverseResolventSolution f D c φ hv
    have hres : IsTransverseResolventSolution f D c φ 0 0
        (u : ℝ → ℂ^n) (w : ℝ → ℂ^n) := by
      simpa [u, coe_complexBUC2OfTransverseResolventSolution] using hv
    have hresEq : challengeResolventMap D c A 0 0 u = w :=
      operatorEquation_of_isTransverseResolventSolution f D c φ A hA hres
    rw [challengeResolventMap_zero] at hresEq
    exact ⟨u, hresEq⟩

/-- The horizontal front operator, its canonical translation mode, and the adjoint phase
functional form a normalized simple Fredholm zero mode. -/
def horizontalSimpleFredholmZeroMode :
    SimpleFredholmZeroMode (BUC ℝ (ℂ^n)) (ComplexBUC2 (ℂ^n)) where
  inclusion := ComplexBUC2.valueCLM (ℂ^n)
  inclusion_injective := ComplexBUC2.valueCLM_injective (ℂ^n)
  operator := challengeTransverseOperator D c A 0
  mode := translationModeComplexBUC2 f D c φ ψ h₃
  functional := phaseFunctional ψ h₃.integrable
  normalized := by
    exact phaseFunctional_embedded_deriv_eq_one_of_spectralStability h₃
      (translationModeBUC f D c φ ψ h₃)
      (translationModeBUC_apply f D c φ ψ h₃)
  kernel_eq_span := horizontalOperator_kernel_eq_span f D c φ ψ h₃ A hA
  solvable_iff := exists_horizontalOperator_eq_iff_phase_zero f D c φ ψ h₃ A hA

/-- The horizontal operator restricted to the phase-zero complements is a bounded linear
equivalence, exactly as used in the Lyapunov--Schmidt reduction of Proposition 2.1. -/
noncomputable def horizontalComplementEquiv :=
  (horizontalSimpleFredholmZeroMode f D c φ ψ h₃ A hA).complementOperatorEquiv


end

end Planarwave
