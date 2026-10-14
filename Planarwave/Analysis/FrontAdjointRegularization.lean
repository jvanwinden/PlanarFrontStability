/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAdjointEquation
import Planarwave.Analysis.L1Mollification

/-!
# Classical regularizations of the front's adjoint equation

Under the original challenge hypotheses, the supplied integrable adjoint has
smooth BUC approximations converging to it almost everywhere. These satisfy the
exact regularized adjoint equation. Both the adjoint and reaction source have
L1 bounds independent of the regularization index.

This is a step toward the regular representative needed in Lemma 4.2.
`FrontAdjointEstimates` supplies uniform derivative estimates, and
`FrontAdjointRegularity` passes to a classical representative. The variable
reaction coefficient cannot be pulled out of its convolution.
-/

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₃ in
/-- Quantitative L1 control of the unsmoothed adjoint reaction term. -/
theorem integral_norm_frontAdjointReaction_le :
    (∫ z, ‖(fderiv ℝ f (φ z)).adjoint (ψ z)‖) ≤
      ‖realFrontDerivativeCoefficient f D c φ h₁ h₂‖ * ∫ z, ‖ψ z‖ := by
  calc
    _ ≤ ∫ z, ‖realFrontDerivativeCoefficient f D c φ h₁ h₂‖ * ‖ψ z‖ := by
      apply integral_mono (integrable_frontAdjointReaction f D c φ ψ h₁ h₂ h₃).norm
        (h₃.integrable.norm.const_mul _)
      intro z
      calc
        _ ≤ ‖(fderiv ℝ f (φ z)).adjoint‖ * ‖ψ z‖ :=
          ((fderiv ℝ f (φ z)).adjoint).le_opNorm _
        _ = ‖fderiv ℝ f (φ z)‖ * ‖ψ z‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          ((realFrontDerivativeCoefficient f D c φ h₁ h₂).norm_apply_le z) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The adjoint's smooth approximation at index `j`. -/
def frontAdjointRegularization (j : ℕ) : BUC ℝ (ℝ^n) :=
  longitudinalMollification ψ h₃.integrable j

/-- Smooth the product `A* ψ` as a whole, respecting the variable coefficient. -/
def frontAdjointReactionRegularization (j : ℕ) : BUC ℝ (ℝ^n) :=
  longitudinalMollification (fun z ↦ (fderiv ℝ f (φ z)).adjoint (ψ z))
    (integrable_frontAdjointReaction f D c φ ψ h₁ h₂ h₃) j

include h₁ h₂ h₃

/-- Every regularization satisfies the actual classical inhomogeneous adjoint ODE. -/
theorem frontAdjointRegularization_equation (j : ℕ) (z : ℝ) :
    D (deriv (deriv (frontAdjointRegularization f D c φ ψ h₃ j)) z) -
      c • deriv (frontAdjointRegularization f D c φ ψ h₃ j) z +
      frontAdjointReactionRegularization f D c φ ψ h₁ h₂ h₃ j z = 0 :=
  frontAdjoint_smoothing_classicalEquation f D c φ ψ h₁ h₂ h₃
    (longitudinalMollifier j) (longitudinalMollifierFirst j) (longitudinalMollifierSecond j)
    (hasDerivAt_longitudinalMollifier j) (hasDerivAt_longitudinalMollifierFirst j) z

end

end Planarwave
