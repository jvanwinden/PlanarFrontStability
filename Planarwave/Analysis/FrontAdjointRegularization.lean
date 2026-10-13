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

/-- Smooth classical adjoint approximations, with the correct almost-everywhere
limit and index-independent L1 bounds. The derivative integrability assertions
are for each index separately; no uniform derivative bound is asserted here. -/
theorem exists_frontAdjoint_classicalRegularizations :
    ∃ u q : ℕ → BUC ℝ (ℝ^n),
      (∀ j, ContDiff ℝ ∞ (u j : ℝ → ℝ^n) ∧ ContDiff ℝ ∞ (q j : ℝ → ℝ^n)) ∧
      (∀ j, Integrable (u j : ℝ → ℝ^n) ∧ Integrable (deriv (u j)) ∧
        Integrable (deriv (deriv (u j))) ∧ Integrable (q j : ℝ → ℝ^n)) ∧
      (∀ j z, D (deriv (deriv (u j)) z) - c • deriv (u j) z + q j z = 0) ∧
      (∀ j, (∫ z, ‖u j z‖) ≤ ∫ z, ‖ψ z‖) ∧
      (∀ j, (∫ z, ‖q j z‖) ≤
        ‖realFrontDerivativeCoefficient f D c φ h₁ h₂‖ * ∫ z, ‖ψ z‖) ∧
      (∀ᵐ z, Tendsto (fun j ↦ u j z) atTop (𝓝 (ψ z)) ∧
        Tendsto (fun j ↦ q j z) atTop (𝓝 ((fderiv ℝ f (φ z)).adjoint (ψ z)))) := by
  let hq := integrable_frontAdjointReaction f D c φ ψ h₁ h₂ h₃
  refine ⟨frontAdjointRegularization f D c φ ψ h₃,
    frontAdjointReactionRegularization f D c φ ψ h₁ h₂ h₃,
    (fun j ↦ ⟨contDiff_longitudinalMollification h₃.integrable j,
      contDiff_longitudinalMollification hq j⟩),
    (fun j ↦ ⟨integrable_longitudinalMollification h₃.integrable j,
      integrable_deriv_longitudinalMollification h₃.integrable j,
      integrable_deriv_deriv_longitudinalMollification h₃.integrable j,
      integrable_longitudinalMollification hq j⟩),
    frontAdjointRegularization_equation f D c φ ψ h₁ h₂ h₃,
    integral_norm_longitudinalMollification_le h₃.integrable, ?_, ?_⟩
  · intro j
    exact (integral_norm_longitudinalMollification_le hq j).trans
      (integral_norm_frontAdjointReaction_le f D c φ ψ h₁ h₂ h₃)
  · exact (ae_tendsto_longitudinalMollification h₃.integrable).and
      (ae_tendsto_longitudinalMollification hq)

end

end Planarwave
