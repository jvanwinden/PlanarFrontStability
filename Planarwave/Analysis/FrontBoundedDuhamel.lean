/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontBoundedKernelVolterra

/-!
# Time-space Fubini for the Fourier evolution on bounded data

The inverse-frequency Duhamel forcing is jointly strongly measurable, by its
continuous frequency integrand. Its spatial integral is dominated uniformly
over the open time interval by the absolute ordered kernel product. This
justifies the time-space interchange for bounded, not necessarily integrable,
initial data.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ}

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n)) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- Inverted forcing for a bounded spatial datum, evaluated at a transverse point. -/
def frontBoundedDuhamelInverse (t r : ℝ) (x : ℝ^m)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) : BUC ℝ (ℂ^n) :=
  ((2 * Real.pi) ^ m)⁻¹ • ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
    frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ (v (z - x))

/-- Joint strong measurability after frequency integration; no unproved
operator-norm time continuity of a semigroup is used. -/
theorem stronglyMeasurable_frontBoundedDuhamelInverse (t : ℝ)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    StronglyMeasurable (fun p : ℝ × ℝ^m ↦ frontBoundedDuhamelInverse f D c φ h₁ h₂ t p.1 p.2 v z) := by
  let g (p : (ℝ × ℝ^m) × ℝ^m) : BUC ℝ (ℂ^n) :=
    Complex.exp (Complex.I * (⟪p.2, p.1.2⟫ : ℂ)) •
      frontFourierDuhamelIntegrand f D c φ h₁ h₂ t p.1.1 p.2 (v (z - p.1.2))
  have hq : Continuous (fun p : (ℝ × ℝ^m) × ℝ^m ↦ (‖p.2‖ ^ 2 : ℝ)) := by fun_prop
  have hv : Continuous (fun p : (ℝ × ℝ^m) × ℝ^m ↦ v (z - p.1.2)) :=
    v.continuous.comp (continuous_const.sub continuous_fst.snd)
  have hT : Continuous (fun p : (ℝ × ℝ^m) × ℝ^m ↦
      (frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖p.2‖ ^ 2)).realOrbit (v (z - p.1.2)) p.1.1) := by
    have hp := (continuous_frontPencil_realOrbit_joint f D c φ h₁ h₂).comp
      ((Complex.continuous_ofReal.comp hq).prodMk (continuous_fst.fst.prodMk hv))
    simpa only [Function.comp_def, frontLinearizedC0Semigroup_eq_pencil] using! hp
  have hS := (continuous_frontDiffusion_realOrbit_joint D h₁.positive c).comp
    (hq.prodMk (((continuous_const (y := t)).sub continuous_fst.fst).prodMk
      ((frontReactionMultiplication f D c φ h₁ h₂).continuous.comp hT)))
  have hphase : Continuous (fun p : (ℝ × ℝ^m) × ℝ^m ↦
      Complex.exp (Complex.I * (⟪p.2, p.1.2⟫ : ℂ))) := by fun_prop
  have hg : Continuous g := by
    simpa only [g, frontFourierDuhamelIntegrand, Function.comp_def] using! hphase.smul hS
  exact hg.stronglyMeasurable.integral_prod_right'.const_smul (((2 * Real.pi) ^ m)⁻¹ : ℝ)

variable (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₃ in
/-- On the open time interval the inverse forcing is the actual ordered kernel product. -/
theorem frontBoundedDuhamelInverse_eq_kernel_integral (t : NNReal) {r : ℝ}
    (hr : r ∈ Ioo 0 (t : ℝ)) (x : ℝ^m) (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z =
      ∫ y : ℝ^m, frontDiffusionKernel D h₁.positive c ((t : ℝ)-r).toNNReal y
        (frontReactionMultiplication f D c φ h₁ h₂
          (frontFourierKernel f D c φ h₁ h₂ r.toNNReal (x-y) (v (z-x)))) :=
  frontFourierDuhamel_inverse_eq_kernel_convolution f D c φ h₁ h₂ ψ h₃ t hr x (v (z-x))

include h₃ in
/-- Absolute spatial integrability of the inverted forcing on bounded data. -/
theorem integrable_frontBoundedDuhamelInverse_space (t : NNReal) {r : ℝ}
    (hr : r ∈ Ioo 0 (t : ℝ)) (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    Integrable (fun x : ℝ^m ↦ frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z) := by
  simp_rw [frontBoundedDuhamelInverse_eq_kernel_integral f D c φ h₁ h₂ ψ h₃ t hr]
  exact (integrable_orderedConvolution_apply
    (continuous_frontDiffusionKernel D h₁.positive c ((t : ℝ)-r).toNNReal)
    (integrable_frontDiffusionKernel D h₁.positive c h₁.kernel _
      (Real.toNNReal_pos.mpr (sub_pos.mpr hr.2)))
    (continuous_frontFourierKernel f D c φ h₁ h₂ ψ h₃ _ (Real.toNNReal_pos.mpr hr.1))
    (integrable_frontFourierKernel f D c φ h₁ h₂ ψ h₃ _ (Real.toNNReal_pos.mpr hr.1)) _ v z).integral_prod_left

include h₃ in
/-- A spatial absolute-integral bound uniform in the open time split. -/
theorem integral_norm_frontBoundedDuhamelInverse_le (t : NNReal) {r : ℝ}
    (hr : r ∈ Ioo 0 (t : ℝ)) (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    (∫ x : ℝ^m, ‖frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z‖) ≤
      ∫ x : ℝ^m, ∫ y : ℝ^m,
        ‖frontBoundedKernelIntegrand f D c φ h₁ h₂ ((t : ℝ)-r).toNNReal r.toNNReal v (x,y)‖ := by
  simp_rw [frontBoundedDuhamelInverse_eq_kernel_integral f D c φ h₁ h₂ ψ h₃ t hr]
  exact integral_norm_integral_orderedConvolution_apply_le
    (continuous_frontDiffusionKernel D h₁.positive c ((t : ℝ)-r).toNNReal)
    (integrable_frontDiffusionKernel D h₁.positive c h₁.kernel _
      (Real.toNNReal_pos.mpr (sub_pos.mpr hr.2)))
    (continuous_frontFourierKernel f D c φ h₁ h₂ ψ h₃ _ (Real.toNNReal_pos.mpr hr.1))
    (integrable_frontFourierKernel f D c φ h₁ h₂ ψ h₃ _ (Real.toNNReal_pos.mpr hr.1)) _ v z

include h₃ in
/-- Joint time-space Bochner integrability of the inverse forcing on bounded data. -/
theorem integrable_frontBoundedDuhamelInverse (t : NNReal)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    Integrable (fun p : ℝ × ℝ^m ↦ frontBoundedDuhamelInverse f D c φ h₁ h₂ t p.1 p.2 v z)
      ((volume.restrict (Ioc 0 (t : ℝ))).prod volume) := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)))]
  have hm := (stronglyMeasurable_frontBoundedDuhamelInverse f D c φ h₁ h₂ t v z).aestronglyMeasurable
    (μ := (volume.restrict (Ioo 0 (t : ℝ))).prod (volume : Measure (ℝ^m)))
  rw [integrable_prod_iff hm]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact integrable_frontBoundedDuhamelInverse_space f D c φ h₁ h₂ ψ h₃ t hr v z
  · obtain ⟨C, _, κ, _, hb⟩ :=
      exists_frontBoundedKernelIntegrand_integral_norm_bound (m := m) f D c φ h₁ h₂ ψ h₃
    apply (integrable_const (C * Real.exp (κ * t) * ‖v‖)).mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    exact (integral_norm_frontBoundedDuhamelInverse_le f D c φ h₁ h₂ ψ h₃ t hr v z).trans
      (hb t t.2 r hr v)

include h₃ in
/-- The time-space interchange needed to integrate the kernel Volterra equation. -/
theorem frontBoundedDuhamelInverse_integral_swap (t : NNReal)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    (∫ x : ℝ^m, ∫ r in 0..(t : ℝ), frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z) =
      ∫ r in 0..(t : ℝ), ∫ x : ℝ^m, frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z := by
  exact (intervalIntegral_integral_swap (by
    simpa only [uIoc_of_le (show 0 ≤ (t : ℝ) from t.2), Function.uncurry] using!
      integrable_frontBoundedDuhamelInverse f D c φ h₁ h₂ ψ h₃ t v z)).symm

/-- Integrating the kernel Duhamel equation against bounded data is legitimate.
This is an equality of longitudinal BUC functions at each transverse point. -/
theorem frontFourierConvolution_duhamel_pointwise (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v z =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) v z +
        ∫ r in 0..(t : ℝ), ∫ x : ℝ^m, frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z := by
  have hfree := integrable_frontDiffusionKernel (m := m) D h₁.positive c h₁.kernel t ht
  have hi := integrable_frontBoundedDuhamelInverse f D c φ h₁ h₂ ψ h₃ t v z
  have htime : Integrable (fun x : ℝ^m ↦ ∫ r in 0..(t : ℝ),
      frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z) := by
    simp only [intervalIntegral.integral_of_le (show 0 ≤ (t : ℝ) from t.2)]
    exact hi.integral_prod_right
  have he (x : ℝ^m) : frontFourierKernel f D c φ h₁ h₂ t x (v (z-x)) =
      frontDiffusionKernel D h₁.positive c t x (v (z-x)) +
        ∫ r in 0..(t : ℝ), frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z := by
    rw [frontFourierKernel_duhamel f D c φ h₁ h₂ ψ h₃ t ht]
    rw [frontDiffusionKernel_eq_fourierIntegral D h₁.positive c h₁.kernel t ht]
    rfl
  rw [frontFourierConvolutionCLM, operatorConvolutionCLM_apply,
    operatorConvolution_apply (continuous_frontFourierKernel f D c φ h₁ h₂ ψ h₃ t ht)
      (integrable_frontFourierKernel f D c φ h₁ h₂ ψ h₃ t ht)]
  simp_rw [he]
  have hiFree : Integrable (fun x : ℝ^m ↦ frontDiffusionKernel D h₁.positive c t x (v (z-x))) :=
    (BUC.evalCLM (𝕜 := ℂ) z).integrable_comp
      (integrable_operatorConvolution (continuous_frontDiffusionKernel D h₁.positive c t) hfree v)
  rw [integral_add hiFree htime,
    frontBoundedDuhamelInverse_integral_swap f D c φ h₁ h₂ ψ h₃ t v z,
    operatorConvolution_apply (continuous_frontDiffusionKernel D h₁.positive c t) hfree]

/-- The full Fourier convolution satisfies the ordered Volterra equation on
every bounded datum, pointwise in the transverse variable and in longitudinal
BUC norm. A time integral in the full iterated BUC norm is a separate assertion. -/
theorem frontFourierConvolution_volterra_pointwise (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v z =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) v z +
        ∫ r in 0..(t : ℝ), operatorConvolution (μ := volume)
          (frontDiffusionKernel D h₁.positive c ((t : ℝ)-r).toNNReal)
          (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
            (operatorConvolution (μ := volume) (frontFourierKernel f D c φ h₁ h₂ r.toNNReal) v)) z := by
  rw [frontFourierConvolution_duhamel_pointwise f D c φ h₁ h₂ ψ h₃ t ht v z]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (show 0 ≤ (t : ℝ) from t.2)
  intro r hr
  simp_rw [frontBoundedDuhamelInverse_eq_kernel_integral f D c φ h₁ h₂ ψ h₃ t hr]
  exact frontKernel_forcing_on_bounded_data f D c φ h₁ h₂ ψ h₃ _ _
    (Real.toNNReal_pos.mpr (sub_pos.mpr hr.2)) (Real.toNNReal_pos.mpr hr.1) v z

/-- The Fourier evolution differs from principal diffusion by `O(t)` in the
full iterated BUC norm. The bound is uniform over all bounded initial data. -/
theorem exists_frontFourierConvolution_principal_difference_bound :
    ∃ C > 0, ∃ κ > 0, ∀ (t : NNReal) (ht : 0 < t),
      ∀ v : BUC (ℝ^m) (BUC ℝ (ℂ^n)),
        ‖frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v -
          operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) v‖ ≤
            (t : ℝ) * (C * Real.exp (κ * t) * ‖v‖) := by
  obtain ⟨C, hC, κ, hκ, hb⟩ :=
    exists_frontBoundedKernelIntegrand_integral_norm_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨C, hC, κ, hκ, fun t ht v ↦ ?_⟩
  apply (BUC.norm_le (by positivity)).mpr
  intro z
  rw [BUC.sub_apply, frontFourierConvolution_duhamel_pointwise f D c φ h₁ h₂ ψ h₃ t ht v z,
    add_sub_cancel_left]
  have hbound : ∀ᵐ r ∂volume, r ∈ uIoc 0 (t : ℝ) →
      ‖∫ x : ℝ^m, frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z‖ ≤
        C * Real.exp (κ * t) * ‖v‖ := by
    filter_upwards [Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ))] with r hr
    intro hrt
    have hro : r ∈ Ioo 0 (t : ℝ) := by
      rw [uIoc_of_le (show 0 ≤ (t : ℝ) from t.2)] at hrt
      exact hr.mpr hrt
    exact (norm_integral_le_integral_norm _).trans
      ((integral_norm_frontBoundedDuhamelInverse_le f D c φ h₁ h₂ ψ h₃ t hro v z).trans
        (hb t t.2 r hro v))
  simpa only [sub_zero, abs_of_nonneg (show 0 ≤ (t : ℝ) from t.2), mul_comm] using!
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hbound

end

end Planarwave
