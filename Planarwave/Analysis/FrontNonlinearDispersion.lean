/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontRealProfileDerivatives
import Planarwave.Analysis.ScalingVariation

/-!
# The nonlinear dispersion identity

Lemma `lem:ndispersion` of the paper. Differentiating the rescaled front
`φ(z/α)` at `α = 1` gives `-z φ'(z)`. Its longitudinal equation has right
hand side `-2 D φ'' - c φ'`. Pairing this equation with the normalized
adjoint yields `⟨ψ, D φ''⟩ = -c/2`. The cutoff scaling lemma justifies
this pairing directly from the original hypotheses.
-/

open MeasureTheory
open scoped InnerProductSpace Laplacian ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The second derivative of the translation mode belongs to BUC. -/
def realTranslationModeSecondDerivativeBUC : BUC ℝ (ℝ^n) :=
  BUC.postcompCLM realStatePartCLM
    (ComplexBUC2.deriv2 (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃))

theorem hasDerivAt_realTranslationModeDerivativeBUC (z : ℝ) :
    HasDerivAt (realTranslationModeDerivativeBUC f D c φ ψ h₃)
      (realTranslationModeSecondDerivativeBUC f D c φ ψ h₃ z) z := by
  simpa only [realTranslationModeDerivativeBUC, realTranslationModeSecondDerivativeBUC,
    BUC.postcompCLM_apply, Function.comp_def] using!
      realStatePartCLM.hasFDerivAt.comp_hasDerivAt z
        (ComplexBUC2.hasDerivAt_deriv (ℂ^n) (translationModeComplexBUC2 f D c φ ψ h₃) z)

@[simp]
theorem realTranslationModeSecondDerivativeBUC_apply (z : ℝ) :
    realTranslationModeSecondDerivativeBUC f D c φ ψ h₃ z = deriv (deriv (deriv φ)) z := by
  have hd := hasDerivAt_realTranslationModeDerivativeBUC f D c φ ψ h₃ z
  have heq : (realTranslationModeDerivativeBUC f D c φ ψ h₃ : ℝ → ℝ^n) = deriv (deriv φ) :=
    funext (realTranslationModeDerivativeBUC_apply f D c φ ψ h₃)
  rw [heq] at hd
  exact hd.deriv.symm

include h₁ h₂ in
/-- Differentiate the traveling-wave equation to obtain the real kernel mode equation. -/
theorem realTranslationMode_equation (z : ℝ) :
    D (realTranslationModeSecondDerivativeBUC f D c φ ψ h₃ z) +
      c • realTranslationModeDerivativeBUC f D c φ ψ h₃ z +
      fderiv ℝ f (φ z) (realTranslationModeBUC f D c φ ψ h₃ z) = 0 := by
  simp only [realTranslationModeSecondDerivativeBUC_apply,
    realTranslationModeDerivativeBUC_apply, realTranslationModeBUC_apply]
  have hs₁ := (contDiff_infty_iff_deriv.mp h₂.smooth).2
  have hs₂ := (contDiff_infty_iff_deriv.mp hs₁).2
  have hd := ((D.hasFDerivAt.comp_hasDerivAt z
    ((hs₂.differentiable (by simp) z).hasDerivAt)).add
      (((hs₁.differentiable (by simp) z).hasDerivAt).const_smul c)).add
      ((h₁.smooth.differentiable (by simp) (φ z)).hasFDerivAt.comp_hasDerivAt z
        ((h₂.smooth.differentiable (by simp) z).hasDerivAt))
  have heq : (fun z ↦ D (deriv (deriv φ) z) + c • deriv φ z + f (φ z)) = fun _ ↦ 0 := by
    funext z
    simpa only [InnerProductSpace.laplacian_eq_iteratedDeriv_real,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h₂.ode z
  change HasDerivAt (fun z ↦ D (deriv (deriv φ) z) + c • deriv φ z + f (φ z)) _ z at hd
  rw [heq] at hd
  simpa only [deriv_const] using hd.deriv.symm

include h₁ h₂ in
/-- The adjoint annihilates the right side of the scaling-variation equation. -/
theorem realPairing_front_scaling_equation :
    realPairingCLM ψ h₃.integrable
      ((2 : ℝ) • BUC.postcompCLM D (realTranslationModeDerivativeBUC f D c φ ψ h₃) +
        c • realTranslationModeBUC f D c φ ψ h₃) = 0 := by
  exact realPairing_scaling_commutator_eq_zero ψ h₃.integrable D c
    (realFrontDerivativeCoefficient f D c φ h₁ h₂)
    (realTranslationModeBUC f D c φ ψ h₃)
    (realTranslationModeDerivativeBUC f D c φ ψ h₃)
    (realTranslationModeSecondDerivativeBUC f D c φ ψ h₃)
    (hasDerivAt_realTranslationModeBUC f D c φ ψ h₃)
    (hasDerivAt_realTranslationModeDerivativeBUC f D c φ ψ h₃)
    (realTranslationMode_equation f D c φ ψ h₁ h₂ h₃)
    (realPairing_frontLongitudinalExpression_eq_zero f D c φ ψ h₁ h₂ h₃)

include h₁ h₂ h₃ in
/-- Lemma `lem:ndispersion`, with the original measurable adjoint and no
additional regularity or localization assumptions. -/
theorem front_nonlinear_dispersion_identity :
    (∫ z, ⟪ψ z, D (deriv (deriv φ) z)⟫_ℝ) = -c / 2 := by
  have h := realPairing_front_scaling_equation f D c φ ψ h₁ h₂ h₃
  simp only [map_add, map_smul, smul_eq_mul, realPairingCLM_apply, BUC.postcompCLM_apply,
    realTranslationModeDerivativeBUC_apply, realTranslationModeBUC_apply, h₃.normalized, mul_one] at h
  linarith

end

end Planarwave
