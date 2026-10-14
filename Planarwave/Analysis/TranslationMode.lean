/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Definitions
import all Planarwave.Analysis.ChallengeBridge
import all Planarwave.Analysis.PhaseFunctional
import all Planarwave.Analysis.ComplexBUC2
import all Planarwave.Analysis.ProfileProjection

/-!
# The bundled translation mode

The paper's critical eigendirection is `φ'`.  Although `Challenge.lean` does not explicitly state
that this function is BUC, that fact follows directly from the `horizontal_kernel` equivalence by
applying its reverse implication to the unit multiple of `φ'`.  This file records that deduction
and removes the remaining external representative from the phase-functional normalization.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
  (c : ℝ) (φ ψ : ℝ → ℝ^n)

/-- The complexified translation eigenfunction. -/
def translationModeFun (z : ℝ) : ℂ^n := embed (deriv φ z)

/-- The translation eigenfunction belongs to the zero eigenspace, obtained from the reverse
direction of the exact kernel characterization in the challenge assumptions. -/
theorem translationMode_resolvent
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    IsTransverseResolventSolution f D c φ 0 0 (translationModeFun φ) 0 := by
  apply (h₃.horizontal_kernel (translationModeFun φ)).mpr
  refine ⟨1, fun x ↦ ?_⟩
  simp [translationModeFun]

/-- The unbundled translation mode is bounded uniformly continuous. -/
theorem isBUC_translationMode
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) : IsBUC (translationModeFun φ) := by
  have hbuc := (translationMode_resolvent f D c φ ψ h₃).buc 0 (by omega)
  change IsBUC (fun x ↦ embed (deriv φ x))
  simpa only [iteratedDeriv_zero, translationModeFun] using hbuc

/-- The canonical BUC representative of the translation eigenfunction. -/
def translationModeBUC (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    LongitudinalBUC n :=
  BUC.ofIsBUC (isBUC_translationMode f D c φ ψ h₃)

@[simp]
theorem translationModeBUC_apply
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (z : ℝ) :
    translationModeBUC f D c φ ψ h₃ z = embed (deriv φ z) := rfl

/-- The paper's phase functional takes value one on the translation mode. -/
@[simp]
theorem phaseFunctional_translationMode_eq_one
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    phaseFunctional ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) = 1 := by
  exact phaseFunctional_embedded_deriv_eq_one_of_spectralStability h₃
    (translationModeBUC f D c φ ψ h₃) (translationModeBUC_apply f D c φ ψ h₃)

/-! ## The translation mode in the common `BUC²` graph domain -/

/-- The first iterated derivative of the translation mode is BUC. -/
theorem isBUC_iteratedDeriv_one_translationMode
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    IsBUC (iteratedDeriv 1 (translationModeFun φ)) := by
  exact (translationMode_resolvent f D c φ ψ h₃).buc 1 (by omega)

/-- The second iterated derivative of the translation mode is BUC. -/
theorem isBUC_iteratedDeriv_two_translationMode
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    IsBUC (iteratedDeriv 2 (translationModeFun φ)) := by
  exact (translationMode_resolvent f D c φ ψ h₃).buc 2 (by omega)

/-- The canonical translation mode in the paper's common complex graph domain
`BUC²(ℝ, ℂⁿ)`.  Its three BUC components are obtained directly from the `i = 0,1,2`
parts of `translationMode_resolvent.buc`; the derivative identities follow from its `C²`
smoothness. -/
def translationModeComplexBUC2
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) : ComplexBUC2 (ℂ^n) := by
  let modeDeriv : BUC ℝ (ℂ^n) :=
    BUC.ofIsBUC (isBUC_iteratedDeriv_one_translationMode f D c φ ψ h₃)
  let modeDeriv2 : BUC ℝ (ℂ^n) :=
    BUC.ofIsBUC (isBUC_iteratedDeriv_two_translationMode f D c φ ψ h₃)
  refine ⟨((translationModeBUC f D c φ ψ h₃, modeDeriv), modeDeriv2), ?_⟩
  intro z
  have hsmooth := (translationMode_resolvent f D c φ ψ h₃).smooth
  have hdiff0 : Differentiable ℝ (translationModeFun φ) :=
    hsmooth.differentiable (by norm_num)
  have hdiff1 : Differentiable ℝ (deriv (translationModeFun φ)) :=
    hsmooth.differentiable_deriv_two
  have hvalue_eq :
      (translationModeBUC f D c φ ψ h₃ : ℝ → ℂ^n) = translationModeFun φ := by
    funext x
    rfl
  have hderiv_eq : (modeDeriv : ℝ → ℂ^n) = iteratedDeriv 1 (translationModeFun φ) := by
    funext x
    rfl
  have hiteratedDeriv_one :
      iteratedDeriv 1 (translationModeFun φ) = deriv (translationModeFun φ) :=
    iteratedDeriv_one
  have hiteratedDeriv_two :
      iteratedDeriv 2 (translationModeFun φ) = deriv (deriv (translationModeFun φ)) := by
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  constructor
  · rw [hvalue_eq]
    change HasDerivAt (translationModeFun φ) (iteratedDeriv 1 (translationModeFun φ) z) z
    simpa only [iteratedDeriv_one] using (hdiff0 z).hasDerivAt
  · rw [hderiv_eq]
    dsimp only [modeDeriv2]
    change HasDerivAt (iteratedDeriv 1 (translationModeFun φ))
      (iteratedDeriv 2 (translationModeFun φ) z) z
    rw [hiteratedDeriv_one, hiteratedDeriv_two]
    exact (hdiff1 z).hasDerivAt

/-- The graph-domain translation mode has the expected value. -/
@[simp]
theorem translationModeComplexBUC2_apply
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (z : ℝ) :
    translationModeComplexBUC2 f D c φ ψ h₃ z = embed (deriv φ z) :=
  rfl

/-- Its bundled BUC value is the previously defined canonical translation mode. -/
@[simp]
theorem translationModeComplexBUC2_value
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    ComplexBUC2.value (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃) =
      translationModeBUC f D c φ ψ h₃ :=
  rfl

/-- Application of the bundled first derivative. -/
@[simp]
theorem translationModeComplexBUC2_deriv_apply
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (z : ℝ) :
    ComplexBUC2.deriv (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃) z =
      iteratedDeriv 1 (translationModeFun φ) z :=
  rfl

/-- Application of the bundled second derivative. -/
@[simp]
theorem translationModeComplexBUC2_deriv2_apply
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (z : ℝ) :
    ComplexBUC2.deriv2 (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃) z =
      iteratedDeriv 2 (translationModeFun φ) z :=
  rfl

/-! ## The canonical profile projection -/

/-- `P₀` specialized to the canonical bundled translation mode. -/
def translationModeProjection
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    LongitudinalBUC n →L[ℂ] LongitudinalBUC n :=
  profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)

@[simp]
theorem translationModeProjection_apply
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (v : LongitudinalBUC n) :
    translationModeProjection f D c φ ψ h₃ v =
      phaseFunctional ψ h₃.integrable v • translationModeBUC f D c φ ψ h₃ :=
  rfl

end

end Planarwave
