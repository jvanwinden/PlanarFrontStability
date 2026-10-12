/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierInitial
import Planarwave.Analysis.BUCVolterraUniqueness

/-!
# Identification of the Fourier formula with the spatial evolution

Both independently defined evolutions satisfy the same pointwise Volterra
equation. The forcing is integrable after transverse evaluation, and both
trajectories are bounded on finite time intervals. Factorial Volterra
uniqueness therefore identifies them, without presuming that the Fourier
formula already defines a strongly continuous spatial semigroup.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n d : ℕ}

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n)) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- Principal-kernel convolution after the reaction coefficient. The value at
nonpositive lag is immaterial to the Volterra integrals. -/
def frontReactionKernelOperator (s : ℝ) :
    BUC (ℝ^m) (BUC ℝ (ℂ^n)) →L[ℂ] BUC (ℝ^m) (BUC ℝ (ℂ^n)) :=
  if hs : 0 < s then
    (operatorConvolutionCLM (μ := volume) (continuous_frontDiffusionKernel D h₁.positive c s.toNNReal)
      (integrable_frontDiffusionKernel D h₁.positive c h₁.kernel _ (Real.toNNReal_pos.mpr hs))).comp
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂))
  else 0

/-- Positive-lag evaluation is the actual ordered convolution. -/
theorem frontReactionKernelOperator_apply {s : ℝ} (hs : 0 < s)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) :
    frontReactionKernelOperator f D c φ h₁ h₂ s v =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c s.toNNReal)
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂) v) := by
  rw [frontReactionKernelOperator, dif_pos hs]
  rfl

/-- A time-uniform bound for the Volterra coefficient, including arbitrarily small lags. -/
theorem exists_frontReactionKernelOperator_bound :
    ∃ L ≥ 0, ∀ s : ℝ, 0 < s → ‖frontReactionKernelOperator (m := m) f D c φ h₁ h₂ s‖ ≤ L := by
  let M : ℝ := ‖(diffusionBUCCoordinatesEquiv D h₁.positive).toContinuousLinearMap‖ *
    (n * ‖(diffusionBUCCoordinatesEquiv D h₁.positive).symm.toContinuousLinearMap‖)
  let B := frontReactionMultiplication f D c φ h₁ h₂
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M * ‖B‖, by positivity, fun s hs ↦ ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [frontReactionKernelOperator_apply f D c φ h₁ h₂ hs]
  apply (norm_operatorConvolution_le (continuous_frontDiffusionKernel D h₁.positive c s.toNNReal)
    (integrable_frontDiffusionKernel D h₁.positive c h₁.kernel _ (Real.toNNReal_pos.mpr hs)) _).trans
  calc
    _ ≤ M * (‖B‖ * ‖v‖) :=
      mul_le_mul (integral_norm_frontDiffusionKernel_le D h₁.positive c h₁.kernel _
        (Real.toNNReal_pos.mpr hs)) (BUC.norm_postcompCLM_apply_le B v) (norm_nonneg _) hM
    _ = _ := by ring

variable (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₃ in
/-- The Fourier trajectory's operator-form forcing is integrable after transverse evaluation. -/
theorem intervalIntegrable_frontFourier_operator_forcing (t : NNReal)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    IntervalIntegrable (fun r : ℝ ↦ frontReactionKernelOperator f D c φ h₁ h₂ ((t : ℝ)-r)
      (operatorConvolution (μ := volume) (frontFourierKernel f D c φ h₁ h₂ r.toNNReal) v) z) volume 0 t := by
  have hi : IntervalIntegrable (fun r : ℝ ↦ ∫ x : ℝ^m,
      frontBoundedDuhamelInverse f D c φ h₁ h₂ t r x v z) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show 0 ≤ (t : ℝ) from t.2)]
    exact (integrable_frontBoundedDuhamelInverse f D c φ h₁ h₂ ψ h₃ t v z).integral_prod_left
  apply hi.congr_uIoo
  intro r hr
  have hr' : r ∈ Ioo 0 (t : ℝ) := uIoo_of_le (show 0 ≤ (t : ℝ) from t.2) ▸ hr
  simp only [frontReactionKernelOperator, dif_pos (sub_pos.mpr hr'.2),
    ContinuousLinearMap.comp_apply, operatorConvolutionCLM_apply]
  simp_rw [frontBoundedDuhamelInverse_eq_kernel_integral f D c φ h₁ h₂ ψ h₃ t hr']
  exact frontKernel_forcing_on_bounded_data f D c φ h₁ h₂ ψ h₃ _ _
    (Real.toNNReal_pos.mpr (sub_pos.mpr hr'.2)) (Real.toNNReal_pos.mpr hr'.1) v z

/-- The Fourier trajectory satisfies the common Volterra equation. -/
theorem frontFourierConvolution_operator_volterra (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v z =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) v z +
        ∫ r in 0..(t : ℝ), frontReactionKernelOperator f D c φ h₁ h₂ ((t : ℝ)-r)
          (operatorConvolution (μ := volume) (frontFourierKernel f D c φ h₁ h₂ r.toNNReal) v) z := by
  rw [frontFourierConvolution_volterra_pointwise f D c φ h₁ h₂ ψ h₃ t ht v z]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (show 0 ≤ (t : ℝ) from t.2)
  intro r hr
  simp only [frontReactionKernelOperator, dif_pos (sub_pos.mpr hr.2),
    ContinuousLinearMap.comp_apply, operatorConvolutionCLM_apply]

/-- The spatial trajectory's operator-form forcing is integrable after transverse evaluation. -/
theorem intervalIntegrable_frontSpatial_operator_forcing (hd : 2 ≤ d) (t : NNReal)
    (v : BUC (ℝ^d) (ℂ^n)) (z : ℝ^(d-1)) :
    IntervalIntegrable (fun r : ℝ ↦ frontReactionKernelOperator f D c φ h₁ h₂ ((t : ℝ)-r)
      (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r)) z) volume 0 t := by
  let A := BUC.evalCLM (𝕜 := ℂ) (E := BUC ℝ (ℂ^n)) z
  have hi := intervalIntegrable_frontSpatial_kernel_forcing f D c φ h₁ h₂ hd t v
  have hie : IntervalIntegrable (fun r : ℝ ↦ operatorConvolution (μ := volume)
      (frontDiffusionKernel D h₁.positive c ((t : ℝ)-r).toNNReal)
      (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
        (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r))) z) volume 0 t :=
    ⟨A.integrable_comp hi.1, A.integrable_comp hi.2⟩
  apply hie.congr_uIoo
  intro r hr
  have hr' : r ∈ Ioo 0 (t : ℝ) := uIoo_of_le (show 0 ≤ (t : ℝ) from t.2) ▸ hr
  simp only [frontReactionKernelOperator, dif_pos (sub_pos.mpr hr'.2),
    ContinuousLinearMap.comp_apply, operatorConvolutionCLM_apply]

/-- The independent spatial semigroup satisfies the same operator Volterra equation. -/
theorem frontSpatialC0Semigroup_operator_volterra (hd : 2 ≤ d) (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^d) (ℂ^n)) (z : ℝ^(d-1)) :
    spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) z =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) (spatialSlices hd v) z +
        ∫ r in 0..(t : ℝ), frontReactionKernelOperator f D c φ h₁ h₂ ((t : ℝ)-r)
          (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r)) z := by
  let A := BUC.evalCLM (𝕜 := ℂ) (E := BUC ℝ (ℂ^n)) z
  have he := congrArg A (frontSpatialC0Semigroup_kernel_volterra f D c φ h₁ h₂ hd t ht v)
  rw [map_add, ← A.intervalIntegral_comp_comm
    (intervalIntegrable_frontSpatial_kernel_forcing f D c φ h₁ h₂ hd t v)] at he
  change _ = _ + ∫ r in 0..(t : ℝ), operatorConvolution (μ := volume)
    (frontDiffusionKernel D h₁.positive c ((t : ℝ)-r).toNNReal)
    (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
      (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r))) z at he
  simp only [A, BUC.evalCLM_apply] at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (show 0 ≤ (t : ℝ) from t.2)
  intro r hr
  simp only [frontReactionKernelOperator, dif_pos (sub_pos.mpr hr.2),
    ContinuousLinearMap.comp_apply, operatorConvolutionCLM_apply]

/-- The first Fourier representation in the paper: the actual spatial evolution
is convolution with the full inverse-frequency kernel on every spatial BUC datum. -/
theorem frontSpatialC0Semigroup_eq_fourierConvolution (hd : 2 ≤ d) (T : NNReal) (hT : 0 < T)
    (v : BUC (ℝ^d) (ℂ^n)) :
    spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd T v) =
      frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ T hT (spatialSlices hd v) := by
  let S := frontSpatialC0Semigroup f D c φ h₁ h₂ hd
  let A := frontReactionKernelOperator (m := d-1) f D c φ h₁ h₂
  let u : ℝ → BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n)) := fun r ↦
    operatorConvolution (μ := volume) (frontFourierKernel f D c φ h₁ h₂ r.toNNReal) (spatialSlices hd v)
  let a : ℝ → BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n)) := fun r ↦ spatialSlices hd (S.realOrbit v r)
  let q : ℝ → BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n)) := fun r ↦
    operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c r.toNNReal) (spatialSlices hd v)
  obtain ⟨L, hL, hbA⟩ := exists_frontReactionKernelOperator_bound (m := d-1) f D c φ h₁ h₂
  obtain ⟨C, hC, κ, hκ, hbF⟩ :=
    exists_frontFourierConvolution_allTime_bound (m := d-1) f D c φ h₁ h₂ ψ h₃
  obtain ⟨M, hM, hbS⟩ := S.exists_local_bound T
  have hu : ∀ r ∈ Ioc 0 (T : ℝ), ‖u r‖ ≤ C * Real.exp (κ * T) * ‖spatialSlices hd v‖ := by
    intro r hr
    have hrr : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr.1
    change ‖frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ r.toNNReal hrr (spatialSlices hd v)‖ ≤ _
    apply ((frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ r.toNNReal hrr).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (hbF _ hrr).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    rw [Real.coe_toNNReal _ hr.1.le]
    exact mul_le_mul_of_nonneg_left hr.2 hκ.le
  have ha : ∀ r ∈ Ioc 0 (T : ℝ), ‖a r‖ ≤ M * ‖v‖ := by
    intro r hr
    dsimp only [a]
    rw [norm_spatialSlices]
    exact ((S r.toNNReal).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbS _ (Real.toNNReal_le_iff_le_coe.mpr hr.2)) (norm_nonneg v))
  have hiu : ∀ r ∈ Ioc 0 (T : ℝ), ∀ z, IntervalIntegrable (fun s ↦ A (r-s) (u s) z) volume 0 r := by
    intro r hr z
    simpa only [A, u, Real.coe_toNNReal _ hr.1.le] using!
      intervalIntegrable_frontFourier_operator_forcing f D c φ h₁ h₂ ψ h₃ r.toNNReal (spatialSlices hd v) z
  have hia : ∀ r ∈ Ioc 0 (T : ℝ), ∀ z, IntervalIntegrable (fun s ↦ A (r-s) (a s) z) volume 0 r := by
    intro r hr z
    simpa only [A, a, S, Real.coe_toNNReal _ hr.1.le] using!
      intervalIntegrable_frontSpatial_operator_forcing f D c φ h₁ h₂ hd r.toNNReal v z
  have heu : ∀ r ∈ Ioc 0 (T : ℝ), ∀ z, u r z = q r z + ∫ s in 0..r, A (r-s) (u s) z := by
    intro r hr z
    simpa only [u, q, A, frontFourierConvolutionCLM, operatorConvolutionCLM_apply,
      Real.coe_toNNReal _ hr.1.le] using!
      frontFourierConvolution_operator_volterra f D c φ h₁ h₂ ψ h₃ r.toNNReal
        (Real.toNNReal_pos.mpr hr.1) (spatialSlices hd v) z
  have hea : ∀ r ∈ Ioc 0 (T : ℝ), ∀ z, a r z = q r z + ∫ s in 0..r, A (r-s) (a s) z := by
    intro r hr z
    simpa only [a, q, A, S, C0Semigroup.realOrbit, Real.coe_toNNReal _ hr.1.le] using!
      frontSpatialC0Semigroup_operator_volterra f D c φ h₁ h₂ hd r.toNNReal
        (Real.toNNReal_pos.mpr hr.1) v z
  have he := bounded_pointwise_volterra_unique A u a q hL (by positivity)
    (mul_nonneg (zero_le_one.trans hM) (norm_nonneg v)) hbA hu ha hiu hia heu hea
    (t := (T : ℝ)) ⟨hT, le_rfl⟩
  simpa only [u, a, S, Real.toNNReal_coe, C0Semigroup.realOrbit_coe,
    frontFourierConvolutionCLM, operatorConvolutionCLM_apply] using! he.symm

/-- The spatial semigroup itself, not just a Fourier candidate, decomposes into
the transverse critical heat evolution and the constructed remainder. -/
theorem frontSpatialC0Semigroup_decomposition (hd : 2 ≤ d) (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^d) (ℂ^n)) :
    spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) =
      frontCriticalHeatEvolution f D c φ ψ h₃ t (spatialSlices hd v) +
        frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht (spatialSlices hd v) := by
  rw [frontSpatialC0Semigroup_eq_fourierConvolution f D c φ h₁ h₂ ψ h₃ hd t ht v,
    frontFourierConvolutionCLM_decomposition]

/-- The long-time `C/t` remainder estimate now holds for the independently
constructed spatial semigroup in the original spatial supremum norm. -/
theorem exists_frontSpatialC0Semigroup_heat_difference_bound (hd : 2 ≤ d) :
    ∃ C > 0, ∀ (t : NNReal), 1 ≤ t → ∀ v : BUC (ℝ^d) (ℂ^n),
      ‖spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) -
        frontCriticalHeatEvolution f D c φ ψ h₃ t (spatialSlices hd v)‖ ≤ (C / t) * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ :=
    exists_frontFourierConvolution_heat_difference_bound (m := d-1) f D c φ h₁ h₂ ψ h₃
  refine ⟨C, hC, fun t ht v ↦ ?_⟩
  have hpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [frontSpatialC0Semigroup_eq_fourierConvolution f D c φ h₁ h₂ ψ h₃ hd t hpos v]
  simpa only [norm_spatialSlices] using! hb t hpos ht (spatialSlices hd v)

end

end Planarwave
