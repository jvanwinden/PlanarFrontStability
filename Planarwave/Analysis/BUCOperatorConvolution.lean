/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Operator-valued convolution on BUC

An integrable continuous operator-valued kernel acts boundedly on BUC, with
operator norm at most its `L¹` norm. We integrate directly in the BUC space;
evaluation commutes with this integral and gives the usual convolution formula.
-/

open MeasureTheory

noncomputable section

namespace BUC

variable {V E F 𝕜 : Type*} [NormedAddCommGroup V]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Postcomposition is itself a bounded linear operation on operators. -/
def postcompOperatorCLM : (E →L[𝕜] F) →L[𝕜] BUC V E →L[𝕜] BUC V F :=
  LinearMap.mkContinuous
    { toFun := fun A : E →L[𝕜] F ↦ postcompCLM (α := V) A
      map_add' := by intros; ext v x; rfl
      map_smul' := by intros; ext v x; rfl }
    1 fun A ↦ by
      change ‖postcompCLM (α := V) A‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound (postcompCLM (α := V) A) (norm_nonneg A)
        (norm_postcompCLM_apply_le A)

@[simp]
theorem postcompOperatorCLM_apply (A : E →L[𝕜] F) :
    postcompOperatorCLM (V := V) A = postcompCLM A := rfl

end BUC

namespace Planarwave

variable {V E F 𝕜 : Type*} [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure V}

/-- Convolution with an operator-valued kernel, as an integral in BUC. -/
def operatorConvolution (K : V → E →L[𝕜] F) (v : BUC V E) : BUC V F :=
  ∫ x, BUC.postcompCLM (K x) (BUC.translate x v) ∂μ

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Integrability in the supremum norm, not merely at individual evaluation points. -/
theorem integrable_operatorConvolution {K : V → E →L[𝕜] F}
    (hK : Continuous K) (hi : Integrable K μ) (v : BUC V E) :
    Integrable (fun x ↦ BUC.postcompCLM (K x) (BUC.translate x v)) μ := by
  have hc : Continuous (fun x ↦ BUC.postcompCLM (K x) (BUC.translate x v)) :=
    ((BUC.postcompOperatorCLM (V := V) (𝕜 := 𝕜) (E := E) (F := F)).continuous.comp hK).clm_apply
      (BUC.continuous_translate v)
  apply (hi.norm.mul_const ‖v‖).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [BUC.norm_translate] using BUC.norm_postcompCLM_apply_le (K x) (BUC.translate x v)

/-- Evaluation of the BUC integral gives the ordinary convolution formula. -/
theorem operatorConvolution_apply {K : V → E →L[𝕜] F}
    (hK : Continuous K) (hi : Integrable K μ) (v : BUC V E) (y : V) :
    operatorConvolution (μ := μ) K v y = ∫ x, K x (v (y - x)) ∂μ := by
  exact ((BUC.evalCLM (𝕜 := 𝕜) (E := F) y).integral_comp_comm
    (integrable_operatorConvolution hK hi v)).symm

omit [CompleteSpace F] in
/-- Addition of integrable kernels is addition of their BUC convolutions. -/
theorem operatorConvolution_add {K L : V → E →L[𝕜] F}
    (hK : Continuous K) (hiK : Integrable K μ)
    (hL : Continuous L) (hiL : Integrable L μ) (v : BUC V E) :
    operatorConvolution (μ := μ) (fun x ↦ K x + L x) v =
      operatorConvolution (μ := μ) K v + operatorConvolution (μ := μ) L v := by
  have he (x : V) : BUC.postcompCLM (K x + L x) (BUC.translate x v) =
      BUC.postcompCLM (K x) (BUC.translate x v) +
        BUC.postcompCLM (L x) (BUC.translate x v) := rfl
  simp only [operatorConvolution, he]
  exact integral_add (integrable_operatorConvolution hK hiK v)
    (integrable_operatorConvolution hL hiL v)

omit [BorelSpace V] [SecondCountableTopology V] [CompleteSpace F] in
/-- Real normalization factors commute with BUC convolution. -/
theorem operatorConvolution_real_smul (r : ℝ) (K : V → E →L[𝕜] F) (v : BUC V E) :
    operatorConvolution (μ := μ) (fun x ↦ r • K x) v =
      r • operatorConvolution (μ := μ) K v := by
  have he (x : V) : BUC.postcompCLM (r • K x) (BUC.translate x v) =
      r • BUC.postcompCLM (K x) (BUC.translate x v) := rfl
  simp only [operatorConvolution, he, integral_smul]

omit [CompleteSpace F] in
/-- The standard `L¹`-to-supremum convolution estimate. -/
theorem norm_operatorConvolution_le {K : V → E →L[𝕜] F}
    (hK : Continuous K) (hi : Integrable K μ) (v : BUC V E) :
    ‖operatorConvolution (μ := μ) K v‖ ≤ (∫ x, ‖K x‖ ∂μ) * ‖v‖ := by
  calc
    _ ≤ ∫ x, ‖BUC.postcompCLM (K x) (BUC.translate x v)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖K x‖ * ‖v‖ ∂μ := by
      apply integral_mono (integrable_operatorConvolution hK hi v).norm (hi.norm.mul_const _) (fun x ↦ ?_)
      simpa only [BUC.norm_translate] using BUC.norm_postcompCLM_apply_le (K x) (BUC.translate x v)
    _ = _ := integral_mul_const _ _

/-- Operator-valued convolution as a bounded linear map between BUC spaces. -/
def operatorConvolutionCLM {K : V → E →L[𝕜] F} (hK : Continuous K) (hi : Integrable K μ) :
    BUC V E →L[𝕜] BUC V F :=
  LinearMap.mkContinuous
    { toFun := operatorConvolution (μ := μ) K
      map_add' := by
        intro v w
        unfold operatorConvolution
        have he (x : V) : BUC.translate x (v + w) = BUC.translate x v + BUC.translate x w := rfl
        simp_rw [he, map_add]
        exact integral_add (integrable_operatorConvolution hK hi v) (integrable_operatorConvolution hK hi w)
      map_smul' := by
        intro a v
        unfold operatorConvolution
        have he (x : V) : BUC.translate x (a • v) = a • BUC.translate x v := rfl
        simp_rw [he, map_smul]
        exact integral_smul a _ }
    (∫ x, ‖K x‖ ∂μ) (norm_operatorConvolution_le hK hi)

omit [CompleteSpace F] in
@[simp]
theorem operatorConvolutionCLM_apply {K : V → E →L[𝕜] F}
    (hK : Continuous K) (hi : Integrable K μ) (v : BUC V E) :
    operatorConvolutionCLM hK hi v = operatorConvolution (μ := μ) K v := rfl

omit [CompleteSpace F] in
/-- The operator norm is bounded by the integral of the kernel's operator norm. -/
theorem norm_operatorConvolutionCLM_le {K : V → E →L[𝕜] F}
    (hK : Continuous K) (hi : Integrable K μ) :
    ‖operatorConvolutionCLM hK hi‖ ≤ ∫ x, ‖K x‖ ∂μ :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ ↦ norm_nonneg _) (norm_operatorConvolution_le hK hi)

end Planarwave
