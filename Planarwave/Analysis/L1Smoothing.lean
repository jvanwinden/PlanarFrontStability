/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCCompactSupport
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-!
# Smoothing an integrable weight by scalar BUC kernels

This supplies classical approximations of the measurable adjoint in the
paper. Derivatives fall on the kernel, so no derivative of the integrable
weight is assumed. Compactly supported smooth kernels give smooth integrable
approximations with integrable derivatives.
-/

open MeasureTheory Filter Set
open scoped ContDiff Convolution

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Convolve an integrable vector-valued weight with a bounded scalar kernel. -/
def l1Smoothing (η : BUC ℝ ℝ) (u : ℝ → F) (x : ℝ) : F :=
  ∫ z, η (x - z) • u z

omit [CompleteSpace F] in
theorem integrable_l1Smoothing_integrand (η : BUC ℝ ℝ) {u : ℝ → F}
    (hu : Integrable u) (x : ℝ) : Integrable (fun z ↦ η (x - z) • u z) :=
  (η.comp (fun z ↦ x - z) (uniformContinuous_const.sub uniformContinuous_id)).integrable_smul hu

omit [CompleteSpace F] in
theorem norm_l1Smoothing_le (η : BUC ℝ ℝ) {u : ℝ → F} (hu : Integrable u) (x : ℝ) :
    ‖l1Smoothing η u x‖ ≤ ‖η‖ * ∫ z, ‖u z‖ := by
  calc
    _ ≤ ∫ z, ‖η‖ * ‖u z‖ := norm_integral_le_of_norm_le (hu.norm.const_mul ‖η‖)
      (ae_of_all _ fun z ↦ by rw [norm_smul]; gcongr; exact η.norm_apply_le _)
    _ = _ := integral_const_mul _ _

omit [CompleteSpace F] in
theorem norm_l1Smoothing_sub_le (η : BUC ℝ ℝ) {u : ℝ → F} (hu : Integrable u)
    (x y : ℝ) {C : ℝ} (hC : ∀ z, ‖η (x - z) - η (y - z)‖ ≤ C) :
    ‖l1Smoothing η u x - l1Smoothing η u y‖ ≤ C * ∫ z, ‖u z‖ := by
  rw [l1Smoothing, l1Smoothing, ← integral_sub
    (integrable_l1Smoothing_integrand η hu x) (integrable_l1Smoothing_integrand η hu y)]
  calc
    _ ≤ ∫ z, C * ‖u z‖ := norm_integral_le_of_norm_le (hu.norm.const_mul C)
      (ae_of_all _ fun z ↦ by rw [← sub_smul, norm_smul]; exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

omit [CompleteSpace F] in
theorem uniformContinuous_l1Smoothing (η : BUC ℝ ℝ) {u : ℝ → F} (hu : Integrable u) :
    UniformContinuous (l1Smoothing η u) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  let M := ∫ z, ‖u z‖
  have hM : 0 ≤ M := integral_nonneg fun _ ↦ norm_nonneg _
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp η.uniformContinuous
    (ε / (M + 1)) (by positivity)
  refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ ε / (M + 1) * M := norm_l1Smoothing_sub_le η hu x y fun z ↦ by
      rw [← dist_eq_norm]
      exact (hmod (by simpa only [dist_sub_right] using hxy)).le
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < M + 1)]
      nlinarith

/-- Smoothing an L1 weight produces bounded uniformly continuous data. -/
def l1SmoothingBUC (η : BUC ℝ ℝ) (u : ℝ → F) (hu : Integrable u) : BUC ℝ F where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup (l1Smoothing η u)
    (uniformContinuous_l1Smoothing η hu).continuous
    (‖η‖ * ∫ z, ‖u z‖) (norm_l1Smoothing_le η hu)
  uniformContinuous' := uniformContinuous_l1Smoothing η hu

omit [CompleteSpace F] in
@[simp]
theorem l1SmoothingBUC_apply (η : BUC ℝ ℝ) (u : ℝ → F) (hu : Integrable u) (x : ℝ) :
    l1SmoothingBUC η u hu x = l1Smoothing η u x := rfl

omit [CompleteSpace F] in
theorem norm_l1SmoothingBUC_le (η : BUC ℝ ℝ) (u : ℝ → F) (hu : Integrable u) :
    ‖l1SmoothingBUC η u hu‖ ≤ ‖η‖ * ∫ z, ‖u z‖ :=
  (BUC.norm_le (mul_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _))).mpr
    (norm_l1Smoothing_le η hu)

omit [CompleteSpace F] in
/-- Differentiate an L1 convolution using a bounded derivative of the kernel. -/
theorem hasDerivAt_l1Smoothing (η η₁ : BUC ℝ ℝ)
    (hη : ∀ x, HasDerivAt η (η₁ x) x) {u : ℝ → F} (hu : Integrable u) (x : ℝ) :
    HasDerivAt (l1Smoothing η u) (l1Smoothing η₁ u x) x := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x z ↦ η (x - z) • u z) (F' := fun x z ↦ η₁ (x - z) • u z)
    (bound := fun z ↦ ‖η₁‖ * ‖u z‖) (s := univ) (μ := volume) Filter.univ_mem
    (Filter.Eventually.of_forall fun x ↦ (integrable_l1Smoothing_integrand η hu x).aestronglyMeasurable)
    (integrable_l1Smoothing_integrand η hu x)
    (integrable_l1Smoothing_integrand η₁ hu x).aestronglyMeasurable
    (ae_of_all _ fun z x _ ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (η₁.norm_apply_le _) (norm_nonneg _))
    (hu.norm.const_mul ‖η₁‖)
    (ae_of_all _ fun z x _ ↦ by
      simpa only [mul_one, Function.comp_def, id_eq] using!
        ((hη (x - z)).comp x ((hasDerivAt_id x).sub_const z)).smul_const (u z))).2

omit [CompleteSpace F] in
/-- If the scalar kernel is integrable as well, so is the smoothed weight. -/
theorem integrable_l1Smoothing (η : BUC ℝ ℝ) (hη : Integrable (η : ℝ → ℝ))
    {u : ℝ → F} (hu : Integrable u) : Integrable (l1Smoothing η u) :=
  hu.integrable_convolution ((ContinuousLinearMap.lsmul ℝ ℝ).flip) hη

omit [CompleteSpace F] in
/-- The L1 convolution estimate, uniform in the shape of the smoothing kernel. -/
theorem integral_norm_l1Smoothing_le (η : BUC ℝ ℝ) (hη : Integrable (η : ℝ → ℝ))
    {u : ℝ → F} (hu : Integrable u) :
    (∫ x, ‖l1Smoothing η u x‖) ≤ (∫ x, ‖η x‖) * ∫ z, ‖u z‖ := by
  have hprod : Integrable (fun p : ℝ × ℝ ↦ ‖η (p.1 - p.2)‖ * ‖u p.2‖) :=
    hu.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ).flip hη.norm
  calc
    _ ≤ ∫ x, ∫ z, ‖η (x - z)‖ * ‖u z‖ := by
      apply integral_mono_ae (integrable_l1Smoothing η hη hu).norm hprod.integral_prod_left
      filter_upwards [hprod.prod_right_ae] with x hx
      exact norm_integral_le_of_norm_le hx (ae_of_all _ fun z ↦ by simp only [norm_smul]; rfl)
    _ = ∫ z, ∫ x, ‖η (x - z)‖ * ‖u z‖ := integral_integral_swap hprod
    _ = (∫ x, ‖η x‖) * ∫ z, ‖u z‖ := by
      simp only [integral_mul_const, integral_sub_right_eq_self (fun x ↦ ‖η x‖), integral_const_mul]

omit [CompleteSpace F] in
/-- Compactly supported smooth kernels produce genuine smooth functions. -/
theorem contDiff_l1Smoothing (η : BUC ℝ ℝ) (hη : ContDiff ℝ ∞ (η : ℝ → ℝ))
    (hc : HasCompactSupport (η : ℝ → ℝ)) {u : ℝ → F} (hu : Integrable u) :
    ContDiff ℝ ∞ (l1Smoothing η u) :=
  hc.contDiff_convolution_right (n := ⊤) ((ContinuousLinearMap.lsmul ℝ ℝ).flip) hu.locallyIntegrable hη

end

end Planarwave
