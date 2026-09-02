/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSmoothing
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
# Multidimensional Gaussian Hermite kernels

This file develops the finite-dimensional part of the Gaussian-kernel proof of Lemma 3.2 in
the paper.  For bounded uniformly continuous Banach-valued data it defines the first Hermite
kernel and the radial second Hermite kernel which represents the Laplacian.

The estimates are dimension-explicit.  They are formulated independently of a choice of
orthonormal basis, which is the form needed for the transverse heat flow in the paper.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

section GaussianMoments

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The exact second radial moment of a standard Gaussian in a Euclidean space. -/
theorem integral_sq_norm_stdGaussian :
    ∫ z : E, ‖z‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      ∫ z : E, ⟪b i, z⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    have hmean : ∫ z : E, ⟪b i, z⟫ ∂(stdGaussian E) = 0 := by
      simpa [innerSL_apply_apply] using
        (integral_strongDual_stdGaussian (innerSL ℝ (b i)))
    have hvar := variance_dual_stdGaussian (innerSL ℝ (b i))
    rw [variance_eq_integral (by fun_prop)] at hvar
    simpa [innerSL_apply_apply, hmean] using hvar
  calc
    ∫ z : E, ‖z‖ ^ 2 ∂(stdGaussian E) =
        ∫ z : E, ∑ i : Fin (Module.finrank ℝ E), ⟪b i, z⟫ ^ 2 ∂(stdGaussian E) := by
      congr 1
      funext z
      exact (b.sum_sq_inner_right z).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        ∫ z : E, ⟪b i, z⟫ ^ 2 ∂(stdGaussian E) := by
      apply integral_finset_sum
      intro i _
      exact ((innerSL ℝ (b i)).comp_memLp'
        (IsGaussian.memLp_two_id : MemLp (id : E → E) 2 (stdGaussian E))).integrable_sq
    _ = Module.finrank ℝ E := by simp [hcoord]

/-- The squared norm of a standard Gaussian is integrable. -/
theorem integrable_sq_norm_stdGaussian :
    Integrable (fun z : E => ‖z‖ ^ 2) (stdGaussian E) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_two_id : MemLp (id : E → E) 2 (stdGaussian E)).integrable_norm_pow
      (by norm_num)

/-- A convenient dimension-explicit first radial moment bound.  It is sharp in dimension one
for the elementary inequality used here and avoids special functions. -/
theorem integral_norm_stdGaussian_le :
    ∫ z : E, ‖z‖ ∂(stdGaussian E) ≤ (Module.finrank ℝ E + 1 : ℝ) / 2 := by
  have hpoint (z : E) : ‖z‖ ≤ (‖z‖ ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg (‖z‖ - 1)]
  calc
    ∫ z : E, ‖z‖ ∂(stdGaussian E) ≤
        ∫ z : E, (‖z‖ ^ 2 + 1) / 2 ∂(stdGaussian E) := by
      exact integral_mono
        (IsGaussian.integrable_id : Integrable (id : E → E) (stdGaussian E)).norm
        ((integrable_sq_norm_stdGaussian.add (integrable_const 1)).div_const 2) hpoint
    _ = (Module.finrank ℝ E + 1 : ℝ) / 2 := by
      rw [integral_div, integral_add, integral_sq_norm_stdGaussian]
      · simp
      · exact integrable_sq_norm_stdGaussian
      · exact integrable_const 1

/-- The radial second Hermite polynomial has `L¹` norm at most twice the dimension. -/
theorem integral_abs_sq_norm_sub_finrank_stdGaussian_le :
    ∫ z : E, |‖z‖ ^ 2 - Module.finrank ℝ E| ∂(stdGaussian E) ≤
      2 * Module.finrank ℝ E := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := by positivity
  have hint : Integrable (fun z : E => |‖z‖ ^ 2 - n|) (stdGaussian E) := by
    exact (integrable_sq_norm_stdGaussian.sub (integrable_const n)).norm
  calc
    ∫ z : E, |‖z‖ ^ 2 - n| ∂(stdGaussian E) ≤
        ∫ z : E, (‖z‖ ^ 2 + n) ∂(stdGaussian E) := by
      exact integral_mono hint (integrable_sq_norm_stdGaussian.add (integrable_const n))
        (fun z => by rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖z‖])
    _ = (Module.finrank ℝ E : ℝ) + n := by
      rw [integral_add integrable_sq_norm_stdGaussian (integrable_const n),
        integral_sq_norm_stdGaussian]
      simp
    _ = 2 * Module.finrank ℝ E := by
      dsimp [n]
      ring

end GaussianMoments

section HermiteKernels

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- First Hermite kernel for Gaussian smoothing.  At positive scale this is the candidate
Fréchet derivative of `x ↦ ∫ z, f (x + s • z)`. -/
def gaussianGradientKernel (s : ℝ) (f : BUC E F) (x : E) : E →L[ℝ] F :=
  ∫ z, ((1 / s) • innerSL ℝ z).smulRight (f (x + s • z)) ∂(stdGaussian E)

theorem integrable_gaussianGradientKernel (s : ℝ) (f : BUC E F) (x : E) :
    Integrable
      (fun z => ((1 / s) • innerSL ℝ z).smulRight (f (x + s • z)))
      (stdGaussian E) := by
  have hd : Integrable (fun z : E => |1 / s| * ‖z‖ * ‖f‖) (stdGaussian E) := by
    exact (((IsGaussian.integrable_id : Integrable (id : E → E) (stdGaussian E)).norm
      |>.const_mul |1 / s|).mul_const ‖f‖).congr (ae_of_all _ fun z => by simp [mul_assoc])
  refine hd.mono' ?_ ?_
  · have hc₁ : Continuous
        (fun z : E => ContinuousLinearMap.smulRightL ℝ E F
          (((1 / s) • innerSL ℝ (E := E)) z)) :=
      (ContinuousLinearMap.smulRightL ℝ E F).continuous.comp
        (((1 / s) • innerSL ℝ (E := E)).continuous)
    have hc₂ : Continuous (fun z : E => f (x + s • z)) :=
      f.continuous.comp (by fun_prop)
    have hc : Continuous
        (fun z : E => ContinuousLinearMap.smulRightL ℝ E F
          (((1 / s) • innerSL ℝ (E := E)) z) (f (x + s • z))) :=
      hc₁.clm_apply hc₂
    exact hc.aestronglyMeasurable
  filter_upwards with z
  simp only [norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (f.norm_apply_le _) (by positivity)

theorem gaussianGradientKernel_apply (s : ℝ) (f : BUC E F) (x h : E) :
    gaussianGradientKernel s f x h =
      ∫ z, (⟪z, h⟫ / s) • f (x + s • z) ∂(stdGaussian E) := by
  rw [gaussianGradientKernel,
    ContinuousLinearMap.integral_apply (integrable_gaussianGradientKernel s f x) h]
  congr 1
  funext z
  simp [innerSL_apply_apply, div_eq_mul_inv, mul_comm]

/-- The trace-contracted second Hermite kernel.  This is the basis-free candidate Laplacian of
Gaussian smoothing. -/
def gaussianLaplacianKernel (s : ℝ) (f : BUC E F) (x : E) : F :=
  ∫ z, ((‖z‖ ^ 2 - Module.finrank ℝ E) / s ^ 2) • f (x + s • z)
    ∂(stdGaussian E)

end HermiteKernels

end

end Planarwave
