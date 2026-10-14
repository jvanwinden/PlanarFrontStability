/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontCoefficient
import Planarwave.Analysis.LongitudinalPairing
import Planarwave.Analysis.BUCCompactSupport
import Planarwave.Analysis.L1Smoothing

/-!
# The adjoint equation from the original spectral hypotheses

The adjoint regularity used in Proposition 2.1 and Lemma 4.2 must be proved
for an almost-everywhere representative of the supplied integrable weight.
First extract its weak ODE from Fredholm solvability, rather than assuming
that the measurable weight satisfies a classical adjoint equation.
-/

open MeasureTheory
open scoped InnerProductSpace ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ}

/-- The challenge's real embedding, bundled for transporting derivative witnesses. -/
def realStateEmbeddingCLM : ℝ^n →L[ℝ] ℂ^n :=
  LinearMap.toContinuousLinearMap
    { toFun := embed
      map_add' := by intros; ext i; simp [embed]
      map_smul' := by intros; ext i; simp [embed] }

@[simp]
theorem realStateEmbeddingCLM_apply (v : ℝ^n) : realStateEmbeddingCLM v = embed v := rfl

/-- Real BUC derivative data give a legitimate test in the complex graph domain. -/
def embeddedRealBUC2 (v v₁ v₂ : BUC ℝ (ℝ^n))
    (hv : ∀ z, HasDerivAt v (v₁ z) z) (hv₁ : ∀ z, HasDerivAt v₁ (v₂ z) z) :
    ComplexBUC2 (ℂ^n) :=
  ⟨((BUC.postcompCLM realStateEmbeddingCLM v, BUC.postcompCLM realStateEmbeddingCLM v₁),
    BUC.postcompCLM realStateEmbeddingCLM v₂), fun z ↦
    ⟨realStateEmbeddingCLM.hasFDerivAt.comp_hasDerivAt z (hv z),
      realStateEmbeddingCLM.hasFDerivAt.comp_hasDerivAt z (hv₁ z)⟩⟩

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The real longitudinal differential expression evaluated on a BUC two-jet. -/
def realFrontLongitudinalExpression (v v₁ v₂ : BUC ℝ (ℝ^n)) : BUC ℝ (ℝ^n) :=
  BUC.postcompCLM D v₂ + c • v₁ +
    BUC.operatorApply (realFrontDerivativeCoefficient f D c φ h₁ h₂) v

@[simp]
theorem realFrontLongitudinalExpression_apply (v v₁ v₂ : BUC ℝ (ℝ^n)) (z : ℝ) :
    realFrontLongitudinalExpression f D c φ h₁ h₂ v v₁ v₂ z =
      D (v₂ z) + c • v₁ z + fderiv ℝ f (φ z) (v z) := rfl

/-- The complex operator acts on real data by embedding the real differential expression. -/
theorem horizontalOperator_embeddedRealBUC2 (v v₁ v₂ : BUC ℝ (ℝ^n))
    (hv : ∀ z, HasDerivAt v (v₁ z) z) (hv₁ : ∀ z, HasDerivAt v₁ (v₂ z) z) :
    challengeTransverseOperator D c (complexFrontDerivativeCoefficient f D c φ h₁ h₂) 0
      (embeddedRealBUC2 v v₁ v₂ hv hv₁) =
    BUC.postcompCLM realStateEmbeddingCLM (realFrontLongitudinalExpression f D c φ h₁ h₂ v v₁ v₂) := by
  apply BUC.ext
  intro z
  rw [challengeTransverseOperator_apply, complexFrontDerivativeCoefficient_apply]
  change (ContinuousLinearMap.complexify D) (embed (v₂ z)) - (0 : ℂ) ^ 2 • (ContinuousLinearMap.complexify D) (embed (v z)) +
    (c : ℂ) • embed (v₁ z) + (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) (embed (v z)) =
      embed (D (v₂ z) + c • v₁ z + fderiv ℝ f (φ z) (v z))
  simp only [← challengeComplexifyCLM_apply, challengeComplexifyCLM_embed]
  ext i
  simp [embed]

/-- Fredholm solvability forces the real adjoint to annihilate every genuine BUC test jet.
No differentiability of `ψ` is assumed. -/
theorem realPairing_frontLongitudinalExpression_eq_zero (v v₁ v₂ : BUC ℝ (ℝ^n))
    (hv : ∀ z, HasDerivAt v (v₁ z) z) (hv₁ : ∀ z, HasDerivAt v₁ (v₂ z) z) :
    realPairingCLM ψ h₃.integrable
      (realFrontLongitudinalExpression f D c φ h₁ h₂ v v₁ v₂) = 0 := by
  let w := realFrontLongitudinalExpression f D c φ h₁ h₂ v v₁ v₂
  have hzero := (exists_horizontalOperator_eq_iff_phase_zero f D c φ ψ h₃
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂)
    (complexFrontDerivativeCoefficient_apply f D c φ h₁ h₂)
    (BUC.postcompCLM realStateEmbeddingCLM w)).mp
      ⟨embeddedRealBUC2 v v₁ v₂ hv hv₁, horizontalOperator_embeddedRealBUC2 f D c φ h₁ h₂ v v₁ v₂ hv hv₁⟩
  rw [phaseFunctional_apply] at hzero
  simp only [BUC.postcompCLM_apply, realStateEmbeddingCLM_apply, inner_embed] at hzero
  exact_mod_cast hzero

include h₁ h₂ h₃ in
/-- The zeroth-order term in the weak adjoint equation is integrable. -/
theorem integrable_frontAdjointReaction :
    Integrable (fun z ↦ (fderiv ℝ f (φ z)).adjoint (ψ z)) := by
  let A := realFrontDerivativeCoefficient f D c φ h₁ h₂
  have hc : Continuous (fun z ↦ (A z).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp A.continuous
  refine (h₃.integrable.norm.const_mul ‖A‖).mono' ?_ ?_
  · have heval : Continuous (fun p : (ℝ^n →L[ℝ] ℝ^n) × ℝ^n ↦ p.1 p.2) := by fun_prop
    exact heval.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.prodMk h₃.integrable.aestronglyMeasurable)
  · filter_upwards [] with z
    calc
      ‖(A z).adjoint (ψ z)‖ ≤ ‖(A z).adjoint‖ * ‖ψ z‖ := ((A z).adjoint).le_opNorm _
      _ ≤ ‖A‖ * ‖ψ z‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; gcongr; exact A.norm_apply_le z

include h₁ h₂ h₃

/-- The weak adjoint equation tested against a scalar BUC two-jet.
The positive sign on the test derivative corresponds to `-c ψ'` in the adjoint ODE. -/
theorem frontAdjoint_weakEquation_buc (η η₁ η₂ : BUC ℝ ℝ)
    (hη : ∀ z, HasDerivAt η (η₁ z) z) (hη₁ : ∀ z, HasDerivAt η₁ (η₂ z) z) :
    (∫ z, η₂ z • D (ψ z) + (c * η₁ z) • ψ z +
      η z • (fderiv ℝ f (φ z)).adjoint (ψ z)) = 0 := by
  have hi : Integrable (fun z ↦ η₂ z • D (ψ z) + (c * η₁ z) • ψ z +
      η z • (fderiv ℝ f (φ z)).adjoint (ψ z)) :=
    ((η₂.integrable_smul (D.integrable_comp h₃.integrable)).add
      ((c • η₁).integrable_smul h₃.integrable)).add
      (η.integrable_smul (integrable_frontAdjointReaction f D c φ ψ h₁ h₂ h₃))
  apply ext_inner_left ℝ
  intro e
  rw [inner_zero_right]
  change (innerSL ℝ e) _ = 0
  rw [← (innerSL ℝ e).integral_comp_comm hi]
  let v := BUC.smulBUC η (BUC.const ℝ e)
  let v₁ := BUC.smulBUC η₁ (BUC.const ℝ e)
  let v₂ := BUC.smulBUC η₂ (BUC.const ℝ e)
  have hzero := realPairing_frontLongitudinalExpression_eq_zero f D c φ ψ h₁ h₂ h₃
    v v₁ v₂ (fun z ↦ (hη z).smul_const e) (fun z ↦ (hη₁ z).smul_const e)
  change (∫ z, ⟪ψ z, D (η₂ z • e) + c • (η₁ z • e) +
    fderiv ℝ f (φ z) (η z • e)⟫_ℝ) = 0 at hzero
  convert hzero using 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [innerSL_apply_apply, inner_add_right,
    inner_smul_right, map_smul, smul_smul,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← h₁.positive.inner_left_eq_inner_right]
  simp only [real_inner_comm]

/-- In particular the original spectral hypotheses imply the distributional
adjoint ODE against every smooth compactly supported scalar test. -/
theorem frontAdjoint_weakEquation (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) :
    (∫ z, deriv (deriv η) z • D (ψ z) + (c * deriv η z) • ψ z +
      η z • (fderiv ℝ f (φ z)).adjoint (ψ z)) = 0 := by
  have hη₁ := (contDiff_infty_iff_deriv.mp hη).2
  have hη₂ := (contDiff_infty_iff_deriv.mp hη₁).2
  exact frontAdjoint_weakEquation_buc f D c φ ψ h₁ h₂ h₃
    (BUC.ofCompactSupport η hη.continuous hc)
    (BUC.ofCompactSupport (deriv η) hη₁.continuous hc.deriv)
    (BUC.ofCompactSupport (deriv (deriv η)) hη₂.continuous hc.deriv.deriv)
    (fun z ↦ (hη.differentiable (by simp) z).hasDerivAt)
    (fun z ↦ (hη₁.differentiable (by simp) z).hasDerivAt)

/-- Convolving the weak adjoint equation is legitimate at every point. The
variable reaction coefficient stays inside its convolution; no commutation
with multiplication by that coefficient is assumed. -/
theorem frontAdjoint_smoothingEquation (η η₁ η₂ : BUC ℝ ℝ)
    (hη : ∀ z, HasDerivAt η (η₁ z) z) (hη₁ : ∀ z, HasDerivAt η₁ (η₂ z) z) (x : ℝ) :
    D (l1Smoothing η₂ ψ x) - c • l1Smoothing η₁ ψ x +
      l1Smoothing η (fun z ↦ (fderiv ℝ f (φ z)).adjoint (ψ z)) x = 0 := by
  let ηx := η.comp (fun z ↦ x - z) (uniformContinuous_const.sub uniformContinuous_id)
  let η₁x := (-η₁).comp (fun z ↦ x - z) (uniformContinuous_const.sub uniformContinuous_id)
  let η₂x := η₂.comp (fun z ↦ x - z) (uniformContinuous_const.sub uniformContinuous_id)
  have hηx (z : ℝ) : HasDerivAt ηx (η₁x z) z := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using!
      (hη (x - z)).comp z ((hasDerivAt_id z).const_sub x)
  have hη₁x (z : ℝ) : HasDerivAt η₁x (η₂x z) z := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one, neg_neg] using!
      ((hη₁ (x - z)).comp z ((hasDerivAt_id z).const_sub x)).neg
  have hweak := frontAdjoint_weakEquation_buc f D c φ ψ h₁ h₂ h₃ ηx η₁x η₂x hηx hη₁x
  have hi₁ := integrable_l1Smoothing_integrand η₁ h₃.integrable x
  have hi₂ := integrable_l1Smoothing_integrand η₂ h₃.integrable x
  have hiA := integrable_l1Smoothing_integrand η
    (integrable_frontAdjointReaction f D c φ ψ h₁ h₂ h₃) x
  simp only [l1Smoothing]
  have hci : Integrable (fun z ↦ c • (η₁ (x - z) • ψ z)) := hi₁.smul c
  have hsub : Integrable (fun z ↦ D (η₂ (x - z) • ψ z) - c • (η₁ (x - z) • ψ z)) :=
    (D.integrable_comp hi₂).sub hci
  rw [← D.integral_comp_comm hi₂, ← integral_smul c (fun z ↦ η₁ (x - z) • ψ z),
    ← integral_sub (D.integrable_comp hi₂) hci,
    ← integral_add hsub hiA]
  convert hweak using 1
  apply integral_congr_ae
  filter_upwards [] with z
  change D (η₂ (x - z) • ψ z) - c • (η₁ (x - z) • ψ z) +
    η (x - z) • (fderiv ℝ f (φ z)).adjoint (ψ z) =
      η₂ (x - z) • D (ψ z) + (c * -η₁ (x - z)) • ψ z +
        η (x - z) • (fderiv ℝ f (φ z)).adjoint (ψ z)
  simp only [map_smul, smul_smul, mul_neg, neg_smul, sub_eq_add_neg]

/-- The smoothed weak equation is an actual classical differential equation. -/
theorem frontAdjoint_smoothing_classicalEquation (η η₁ η₂ : BUC ℝ ℝ)
    (hη : ∀ z, HasDerivAt η (η₁ z) z) (hη₁ : ∀ z, HasDerivAt η₁ (η₂ z) z) (x : ℝ) :
    D (deriv (deriv (l1Smoothing η ψ)) x) - c • deriv (l1Smoothing η ψ) x +
      l1Smoothing η (fun z ↦ (fderiv ℝ f (φ z)).adjoint (ψ z)) x = 0 := by
  have hfirst : deriv (l1Smoothing η ψ) = l1Smoothing η₁ ψ :=
    funext fun z ↦ (hasDerivAt_l1Smoothing η η₁ hη h₃.integrable z).deriv
  rw [hfirst, (hasDerivAt_l1Smoothing η₁ η₂ hη₁ h₃.integrable x).deriv]
  exact frontAdjoint_smoothingEquation f D c φ ψ h₁ h₂ h₃ η η₁ η₂ hη hη₁ x

end

end Planarwave
