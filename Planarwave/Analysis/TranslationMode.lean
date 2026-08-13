/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Challenge
import all Planarwave.Analysis.ChallengeBridge
import all Planarwave.Analysis.PhaseFunctional

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
  simpa only [translationModeFun] using hbuc

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

/-- Normalization makes the translation mode nonzero. -/
theorem translationModeBUC_ne_zero
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    translationModeBUC f D c φ ψ h₃ ≠ 0 := by
  intro hzero
  have := phaseFunctional_translationMode_eq_one f D c φ ψ h₃
  rw [hzero, map_zero] at this
  norm_num at this

end

end Planarwave
