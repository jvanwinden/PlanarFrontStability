/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.TranslationMode
import all Planarwave.Analysis.FrontAdjointEquation

/-!
# Real BUC profile derivatives

Recover the real profile derivatives from the previously constructed
complex translation mode and its graph-domain derivative. These are the
fixed profiles in the full perturbation source `eq:defNtilde`.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ}

/-- Coordinatewise real part, used to recover the real profile jet. -/
def realStatePartCLM : ℂ^n →L[ℝ] ℝ^n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ WithLp.toLp 2 (fun i ↦ (v i).re)
      map_add' := by intros; ext i; simp
      map_smul' := by intros; ext i; simp }

@[simp]
theorem realStatePartCLM_embed (v : ℝ^n) : realStatePartCLM (embed v) = v := by
  ext i
  simp [realStatePartCLM, embed]

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The actual first profile derivative as a real BUC function. -/
def realTranslationModeBUC : BUC ℝ (ℝ^n) :=
  BUC.postcompCLM realStatePartCLM (translationModeBUC f D c φ ψ h₃)

@[simp]
theorem realTranslationModeBUC_apply (z : ℝ) :
    realTranslationModeBUC f D c φ ψ h₃ z = deriv φ z := by
  simp [realTranslationModeBUC]

/-- The real BUC derivative of the translation mode. -/
def realTranslationModeDerivativeBUC : BUC ℝ (ℝ^n) :=
  BUC.postcompCLM realStatePartCLM
    (ComplexBUC2.deriv (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃))

theorem hasDerivAt_realTranslationModeBUC (z : ℝ) :
    HasDerivAt (realTranslationModeBUC f D c φ ψ h₃)
      (realTranslationModeDerivativeBUC f D c φ ψ h₃ z) z := by
  simpa only [realTranslationModeBUC, realTranslationModeDerivativeBUC,
    BUC.postcompCLM_apply, translationModeComplexBUC2_value, Function.comp_def] using!
      realStatePartCLM.hasFDerivAt.comp_hasDerivAt z
        (ComplexBUC2.hasDerivAt_value (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃) z)

@[simp]
theorem realTranslationModeDerivativeBUC_apply (z : ℝ) :
    realTranslationModeDerivativeBUC f D c φ ψ h₃ z = deriv (deriv φ) z := by
  have hd := hasDerivAt_realTranslationModeBUC f D c φ ψ h₃ z
  have heq : (realTranslationModeBUC f D c φ ψ h₃ : ℝ → ℝ^n) = deriv φ :=
    funext (realTranslationModeBUC_apply f D c φ ψ h₃)
  rw [heq] at hd
  exact hd.deriv.symm

end

end Planarwave
