/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Challenge
import all Planarwave.Analysis.PhaseFunctional
import all Planarwave.Analysis.ProfileProjection
import all Planarwave.Analysis.TranslationMode
import all Planarwave.Analysis.TransverseOperatorBridge
import Planarwave.Analysis.ClosedOperatorFromResolvent
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
  (hA : ∀ z v, A z v = (fderiv ℝ f (φ z)).complexify v)

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

/-- Consequently zero is semisimple: the embedded translation mode is not in the range of the
horizontal operator. -/
theorem translationMode_not_mem_horizontalOperator_range :
    ComplexBUC2.value (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃) ∉
      LinearMap.range (challengeTransverseOperator D c A 0).toLinearMap := by
  exact (horizontalSimpleFredholmZeroMode f D c φ ψ h₃ A hA).inclusion_mode_not_mem_range

/-- The horizontal operator restricted to the phase-zero complements is a bounded linear
equivalence, exactly as used in the Lyapunov--Schmidt reduction of Proposition 2.1. -/
noncomputable def horizontalComplementEquiv :=
  (horizontalSimpleFredholmZeroMode f D c φ ψ h₃ A hA).complementOperatorEquiv

/-! ## Transfer of the challenge spectrum to the bundled pencil -/

include h₃

/-- The horizontal spectral gap, stated directly for failure of bijectivity of the bundled
common-domain resolvent. -/
theorem bundled_horizontal_spectral_gap :
    ∃ θ > 0, ∀ l : ℂ,
      ¬ Function.Bijective (challengeResolventMap D c A 0 l) →
        l = 0 ∨ l.re ≤ -θ := by
  obtain ⟨θ, hθ, hgap⟩ := h₃.horizontal_spectral_gap
  refine ⟨θ, hθ, fun l hl ↦ ?_⟩
  exact hgap l ((mem_transverseSpectrum_iff_not_bijective f D c φ A hA 0 l).2 hl)

/-- The medium/high-wavenumber spectral gap in bundled-operator form. -/
theorem bundled_transverse_high_wavenumber :
    ∀ k₀ > 0, ∃ θ₁ > 0,
      ∀ k ≥ k₀, ∀ l : ℂ,
        ¬ Function.Bijective (challengeResolventMap D c A k l) → l.re ≤ -θ₁ := by
  intro k₀ hk₀
  obtain ⟨θ₁, hθ₁, hgap⟩ := h₃.transverse_high_wavenumber k₀ hk₀
  refine ⟨θ₁, hθ₁, fun k hk l hl ↦ ?_⟩
  exact hgap k hk l
    ((mem_transverseSpectrum_iff_not_bijective f D c φ A hA k l).2 hl)

/-- The positive real number one lies in the horizontal resolvent set.  This follows immediately
from the spectral gap and provides a resolvent point from which closedness of the horizontal
operator is obtained. -/
theorem horizontal_resolventMap_one_bijective :
    Function.Bijective (challengeResolventMap D c A 0 1) := by
  obtain ⟨θ, hθ, hgap⟩ := bundled_horizontal_spectral_gap f D c φ ψ h₃ A hA
  by_contra hnot
  rcases hgap 1 hnot with hone | hle
  · norm_num at hone
  · norm_num at hle
    linarith

/-- The concrete horizontal operator as a closed operator on longitudinal BUC.  Closedness is
derived, rather than assumed, from the resolvent point `1`. -/
def horizontalClosedOperator :
    ClosedOperator ℂ (BUC ℝ (ℂ^n)) (ComplexBUC2 (ℂ^n)) :=
  ClosedOperator.ofBijectiveResolvent
    (ComplexBUC2.valueCLM (ℂ^n))
    (challengeTransverseOperator D c A 0)
    (ComplexBUC2.valueCLM_injective (ℂ^n)) 1
    (by
      change Function.Bijective (challengeResolventMap D c A 0 1)
      exact horizontal_resolventMap_one_bijective f D c φ ψ h₃ A hA)

@[simp]
theorem horizontalClosedOperator_operator :
    (horizontalClosedOperator f D c φ ψ h₃ A hA).operator =
      challengeTransverseOperator D c A 0 :=
  rfl

@[simp]
theorem horizontalClosedOperator_inclusion :
    (horizontalClosedOperator f D c φ ψ h₃ A hA).inclusion =
      ComplexBUC2.valueCLM (ℂ^n) :=
  rfl

@[simp]
theorem horizontalClosedOperator_resolventMap (l : ℂ) :
    (horizontalClosedOperator f D c φ ψ h₃ A hA).resolventMap l =
      challengeResolventMap D c A 0 l :=
  rfl

/-- The spectrum of the concrete closed horizontal operator is exactly the semantic spectrum from
the challenge statement. -/
theorem mem_horizontalClosedOperator_spectrum_iff (l : ℂ) :
    l ∈ (horizontalClosedOperator f D c φ ψ h₃ A hA).spectrum ↔
      l ∈ TransverseSpectrum f D c φ 0 := by
  rw [ClosedOperator.mem_spectrum,
    mem_transverseSpectrum_iff_not_bijective f D c φ A hA 0 l]
  rfl

/-- Zero belongs to the horizontal spectrum because the normalized translation mode is nonzero. -/
theorem zero_mem_horizontalClosedOperator_spectrum :
    (0 : ℂ) ∈ (horizontalClosedOperator f D c φ ψ h₃ A hA).spectrum := by
  rw [ClosedOperator.mem_spectrum]
  intro hbij
  let S := horizontalSimpleFredholmZeroMode f D c φ ψ h₃ A hA
  have hzero : (challengeTransverseOperator D c A 0) S.mode = 0 := S.operator_mode
  have hmap : (horizontalClosedOperator f D c φ ψ h₃ A hA).resolventMap 0 S.mode =
      (horizontalClosedOperator f D c φ ψ h₃ A hA).resolventMap 0 0 := by
    simpa [S] using hzero
  have := hbij.injective hmap
  exact S.mode_ne_zero this

end

end Planarwave
