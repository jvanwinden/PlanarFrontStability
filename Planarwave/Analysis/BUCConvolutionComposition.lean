/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCOperatorConvolution
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-!
# Ordered composition of operator convolutions on bounded data

Two integrable operator kernels and a bounded intermediate operator give an
absolutely integrable double convolution in the BUC norm. Spatial Fubini is
therefore valid without imposing integrability on the initial datum. The order
of the three operators is retained throughout.
-/

open MeasureTheory

namespace Planarwave

noncomputable section

variable {V E : Type*} [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {μ : Measure V} [SFinite μ] [μ.IsAddRightInvariant]

/-- The ordered double convolution integrand, with total displacement first. -/
def orderedConvolutionIntegrand (K L : V → E →L[ℂ] E) (B : E →L[ℂ] E)
    (v : BUC V E) (p : V × V) : BUC V E :=
  BUC.postcompCLM (K p.2)
    (BUC.postcompCLM B (BUC.postcompCLM (L (p.1 - p.2)) (BUC.translate p.1 v)))

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace E] in
/-- Continuity in both spatial integration variables in the full BUC norm. -/
theorem continuous_orderedConvolutionIntegrand {K L : V → E →L[ℂ] E}
    (hK : Continuous K) (hL : Continuous L) (B : E →L[ℂ] E) (v : BUC V E) :
    Continuous (orderedConvolutionIntegrand K L B v) := by
  apply ((BUC.postcompOperatorCLM (V := V)).continuous.comp (hK.comp continuous_snd)).clm_apply
  apply (BUC.postcompCLM B).continuous.comp
  exact ((BUC.postcompOperatorCLM (V := V)).continuous.comp
    (hL.comp (continuous_fst.sub continuous_snd))).clm_apply
      ((BUC.continuous_translate v).comp continuous_fst)

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace E] in
/-- The pointwise majorant separates the two kernel norms from the bounded datum. -/
theorem norm_orderedConvolutionIntegrand_le (K L : V → E →L[ℂ] E)
    (B : E →L[ℂ] E) (v : BUC V E) (p : V × V) :
    ‖orderedConvolutionIntegrand K L B v p‖ ≤
      (‖K p.2‖ * ‖L (p.1 - p.2)‖) * (‖B‖ * ‖v‖) := by
  apply (BUC.norm_postcompCLM_apply_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (BUC.norm_postcompCLM_apply_le _ _) (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (BUC.norm_postcompCLM_apply_le _ _) (norm_nonneg _))
      (norm_nonneg _)).trans_eq
  rw [BUC.norm_translate]
  ring

omit [CompleteSpace E] in
/-- Absolute integrability of the ordered spatial product for arbitrary bounded
uniformly continuous data. In particular, this justifies spatial Fubini. -/
theorem integrable_orderedConvolutionIntegrand {K L : V → E →L[ℂ] E}
    (hK : Continuous K) (hiK : Integrable K μ)
    (hL : Continuous L) (hiL : Integrable L μ) (B : E →L[ℂ] E) (v : BUC V E) :
    Integrable (orderedConvolutionIntegrand K L B v) (μ.prod μ) := by
  have hi : Integrable (fun p : V × V ↦ ‖K p.2‖ * ‖L (p.1 - p.2)‖) (μ.prod μ) :=
    hiK.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hiL.norm
  apply (hi.mul_const (‖B‖ * ‖v‖)).mono'
    (continuous_orderedConvolutionIntegrand hK hL B v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_orderedConvolutionIntegrand_le K L B v)

/-- Spatial Fubini identifies the ordered kernel product acting on bounded data
with composition of the two actual BUC convolution operators. -/
theorem integral_orderedConvolutionIntegrand {K L : V → E →L[ℂ] E}
    (hK : Continuous K) (hiK : Integrable K μ)
    (hL : Continuous L) (hiL : Integrable L μ) (B : E →L[ℂ] E) (v : BUC V E) :
    (∫ x, ∫ y, orderedConvolutionIntegrand K L B v (x, y) ∂μ ∂μ) =
      operatorConvolution (μ := μ) K (BUC.postcompCLM B (operatorConvolution (μ := μ) L v)) := by
  rw [integral_integral_swap (f := fun x y ↦ orderedConvolutionIntegrand K L B v (x, y))
    (integrable_orderedConvolutionIntegrand hK hiK hL hiL B v)]
  unfold operatorConvolution
  apply integral_congr_ae
  filter_upwards [] with y
  let T : BUC V E →L[ℂ] BUC V E :=
    (BUC.postcompCLM (K y)).comp ((BUC.postcompCLM B).comp (BUC.translateCLM y))
  have he (x : V) : orderedConvolutionIntegrand K L B v (x, y) =
      T (BUC.postcompCLM (L (x - y)) (BUC.translate (x - y) v)) := by
    apply BUC.ext
    intro z
    simp only [orderedConvolutionIntegrand, T, ContinuousLinearMap.comp_apply,
      BUC.postcompCLM_apply, BUC.translateCLM_apply, BUC.translate_apply]
    congr 3
    abel_nf
  simp_rw [he]
  rw [integral_sub_right_eq_self (fun x ↦ T (BUC.postcompCLM (L x) (BUC.translate x v))) y]
  rw [T.integral_comp_comm (integrable_operatorConvolution hL hiL v)]
  rfl

omit [CompleteSpace E] in
/-- The absolute double integral is bounded by the product of the kernel masses.
This estimate has no time-split singularities when those masses are uniform. -/
theorem integral_norm_orderedConvolutionIntegrand_le {K L : V → E →L[ℂ] E}
    (hK : Continuous K) (hiK : Integrable K μ)
    (hL : Continuous L) (hiL : Integrable L μ) (B : E →L[ℂ] E) (v : BUC V E) :
    (∫ x, ∫ y, ‖orderedConvolutionIntegrand K L B v (x, y)‖ ∂μ ∂μ) ≤
      (∫ x, ‖K x‖ ∂μ) * (∫ x, ‖L x‖ ∂μ) * (‖B‖ * ‖v‖) := by
  have hi : Integrable (fun p : V × V ↦ ‖K p.2‖ * ‖L (p.1 - p.2)‖) (μ.prod μ) :=
    hiK.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hiL.norm
  rw [integral_integral (integrable_orderedConvolutionIntegrand hK hiK hL hiL B v).norm]
  calc
    _ ≤ ∫ p : V × V, (‖K p.2‖ * ‖L (p.1 - p.2)‖) * (‖B‖ * ‖v‖) ∂(μ.prod μ) :=
      integral_mono (integrable_orderedConvolutionIntegrand hK hiK hL hiL B v).norm
        (hi.mul_const _) (norm_orderedConvolutionIntegrand_le K L B v)
    _ = _ := by
      rw [integral_mul_const, integral_prod_symm _ hi]
      simp only [integral_const_mul, integral_sub_right_eq_self (fun x ↦ ‖L x‖)]
      rw [integral_mul_const]

/-- The same ordered identity in ordinary pointwise integral form. -/
theorem integral_orderedConvolution_apply {K L : V → E →L[ℂ] E}
    (hK : Continuous K) (hiK : Integrable K μ)
    (hL : Continuous L) (hiL : Integrable L μ) (B : E →L[ℂ] E) (v : BUC V E) (z : V) :
    (∫ x, ∫ y, K y (B (L (x - y) (v (z - x)))) ∂μ ∂μ) =
      operatorConvolution (μ := μ) K (BUC.postcompCLM B (operatorConvolution (μ := μ) L v)) z := by
  let A := BUC.evalCLM (𝕜 := ℂ) (E := E) z
  have hi := integrable_orderedConvolutionIntegrand hK hiK hL hiL B v
  have he : (fun p : V × V ↦ K p.2 (B (L (p.1 - p.2) (v (z - p.1))))) =
      fun p ↦ A (orderedConvolutionIntegrand K L B v p) := rfl
  have hi' : Integrable (fun p : V × V ↦ K p.2 (B (L (p.1 - p.2) (v (z - p.1))))) (μ.prod μ) := by
    rw [he]
    exact A.integrable_comp hi
  rw [integral_integral hi']
  change (∫ p : V × V, A (orderedConvolutionIntegrand K L B v p) ∂(μ.prod μ)) = _
  rw [A.integral_comp_comm hi,
    ← integral_integral (f := fun x y ↦ orderedConvolutionIntegrand K L B v (x, y)) hi]
  rw [integral_orderedConvolutionIntegrand hK hiK hL hiL B v]
  rfl

omit [CompleteSpace E] in
/-- Absolute integrability remains valid after evaluating the outer BUC variable. -/
theorem integrable_orderedConvolution_apply {K L : V → E →L[ℂ] E}
    (hK : Continuous K) (hiK : Integrable K μ)
    (hL : Continuous L) (hiL : Integrable L μ) (B : E →L[ℂ] E) (v : BUC V E) (z : V) :
    Integrable (fun p : V × V ↦ K p.2 (B (L (p.1 - p.2) (v (z - p.1))))) (μ.prod μ) :=
  (BUC.evalCLM (𝕜 := ℂ) z).integrable_comp
    (integrable_orderedConvolutionIntegrand hK hiK hL hiL B v)

omit [CompleteSpace E] in
/-- Evaluation and the inner spatial integral can only decrease the absolute
double-integral majorant. -/
theorem integral_norm_integral_orderedConvolution_apply_le {K L : V → E →L[ℂ] E}
    (hK : Continuous K) (hiK : Integrable K μ)
    (hL : Continuous L) (hiL : Integrable L μ) (B : E →L[ℂ] E) (v : BUC V E) (z : V) :
    (∫ x, ‖∫ y, K y (B (L (x - y) (v (z - x)))) ∂μ‖ ∂μ) ≤
      ∫ x, ∫ y, ‖orderedConvolutionIntegrand K L B v (x, y)‖ ∂μ ∂μ := by
  have hi := integrable_orderedConvolutionIntegrand hK hiK hL hiL B v
  have hie := integrable_orderedConvolution_apply hK hiK hL hiL B v z
  calc
    _ ≤ ∫ x, ∫ y, ‖K y (B (L (x - y) (v (z - x))))‖ ∂μ ∂μ :=
      integral_mono hie.integral_prod_left.norm hie.norm.integral_prod_left
        (fun _ ↦ norm_integral_le_integral_norm _)
    _ ≤ _ := by
      rw [integral_integral hie.norm, integral_integral hi.norm]
      exact integral_mono hie.norm hi.norm
        (fun p ↦ BUC.norm_apply_le (orderedConvolutionIntegrand K L B v p) z)

end

end Planarwave
