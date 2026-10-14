/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDirectionalSmoothing
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public section

/-!
# Smoothness of multidimensional heat flow

The first Hermite kernel is bounded uniformly continuous as an operator-valued function.
Spatial differentiation commutes with heat flow on data with a BUC Fréchet derivative.
Splitting a positive time interval in half then proves spatial smoothing to every order,
including for Banach-valued data and in dimension zero.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A modulus of continuity for the datum gives one for the first Hermite kernel. -/
theorem norm_gaussianGradientKernel_sub_le (s : ℝ) (f : BUC E F) (x y : E)
    {C : ℝ} (hC : ∀ z, ‖f (x + s • z) - f (y + s • z)‖ ≤ C) :
    ‖gaussianGradientKernel s f x - gaussianGradientKernel s f y‖ ≤
      (|1 / s| * ∫ z : E, ‖z‖ ∂stdGaussian E) * C := by
  rw [gaussianGradientKernel, gaussianGradientKernel,
    ← integral_sub (integrable_gaussianGradientKernel s f x)
      (integrable_gaussianGradientKernel s f y)]
  calc
    _ ≤ ∫ z : E, |1 / s| * ‖z‖ * C ∂stdGaussian E := by
      apply norm_integral_le_of_norm_le
        (((IsGaussian.integrable_id : Integrable (id : E → E) (stdGaussian E)).norm.const_mul
          |1 / s|).mul_const C)
      filter_upwards with z
      change ‖(ContinuousLinearMap.smulRightL ℝ E F ((1 / s) • innerSL ℝ z))
        (f (x + s • z)) - (ContinuousLinearMap.smulRightL ℝ E F ((1 / s) • innerSL ℝ z))
        (f (y + s • z))‖ ≤ _
      rw [← map_sub]
      change ‖((1 / s) • innerSL ℝ z).smulRight (f (x + s • z) - f (y + s • z))‖ ≤ _
      rw [ContinuousLinearMap.norm_smulRight_apply,
        norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left (hC z) (by positivity)
    _ = _ := by rw [integral_mul_const, integral_const_mul]

/-- Uniform continuity of the first Hermite kernel in operator norm. -/
theorem uniformContinuous_gaussianGradientKernel (s : ℝ) (f : BUC E F) :
    UniformContinuous (gaussianGradientKernel s f) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  let K := |1 / s| * ∫ z : E, ‖z‖ ∂stdGaussian E
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  have hη : 0 < ε / (K + 1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp f.uniformContinuous _ hη
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ K * (ε / (K + 1)) := norm_gaussianGradientKernel_sub_le s f x y fun z => by
      rw [← dist_eq_norm]
      exact (hmod (by simpa only [dist_add_right] using hxy)).le
    _ < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < K + 1)]
      nlinarith

/-- The operator-norm first derivative bound is independent of spatial dimension. -/
theorem norm_fderiv_heatFlow_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (x : E) :
    ‖fderiv ℝ (heatFlow a t f) x‖ ≤ ‖f‖ / heatScale a t := by
  rw [(hasFDerivAt_heatFlow ha ht f x).fderiv]
  exact ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity [heatScale_pos_of_pos ha ht])
    (fun v hv => norm_gaussianGradientKernel_unit_le ha ht v hv f x)

/-- The spatial Fréchet derivative of a positive-time heat orbit is BUC. -/
def heatFDerivBUC {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    BUC E (E →L[ℝ] F) where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup
    (gaussianGradientKernel (heatScale a t) f)
    (uniformContinuous_gaussianGradientKernel _ f).continuous
    (‖f‖ / heatScale a t) (fun x => by
      rw [← (hasFDerivAt_heatFlow ha ht f x).fderiv]
      exact norm_fderiv_heatFlow_le ha ht f x)
  uniformContinuous' := uniformContinuous_gaussianGradientKernel _ f

@[simp]
theorem heatFDerivBUC_apply {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (x : E) :
    heatFDerivBUC ha ht f x = fderiv ℝ (heatFlow a t f) x :=
  (hasFDerivAt_heatFlow ha ht f x).fderiv.symm

/-- The BUC derivative has the same dimension-independent bound. -/
theorem norm_heatFDerivBUC_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    ‖heatFDerivBUC ha ht f‖ ≤ ‖f‖ / heatScale a t := by
  apply (BUC.norm_le (div_nonneg (norm_nonneg _) (heatScale_pos_of_pos ha ht).le)).mpr
  intro x
  rw [heatFDerivBUC_apply]
  exact norm_fderiv_heatFlow_le ha ht f x

/-- Passing a Fréchet derivative through heat averaging when the derivative is BUC. -/
theorem hasFDerivAt_heatFlow_of_hasFDerivAt (a t : ℝ) (f : BUC E F)
    (g : BUC E (E →L[ℝ] F)) (hg : ∀ x, HasFDerivAt f (g x) x) (x : E) :
    HasFDerivAt (heatFlow a t f) (heatFlow a t g x) x := by
  let s := heatScale a t
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x z : E => f (x + s • z))
    (F' := fun x z : E => g (x + s • z))
    (bound := fun _ : E => ‖g‖) (s := univ) (μ := stdGaussian E)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_add_heatScale f.continuous ‖f‖ f.norm_apply_le x)
    ((g.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun z x _ => g.norm_apply_le (x + s • z))
    (integrable_const ‖g‖)
  filter_upwards with z
  intro y _
  simpa [Function.comp_def] using (hg (y + s • z)).comp y ((hasFDerivAt_id y).add_const (s • z))

/-- Fréchet differentiation commutes with heat averaging on BUC differentiable data. -/
theorem fderiv_heatFlow_of_hasFDerivAt (a t : ℝ) (f : BUC E F)
    (g : BUC E (E →L[ℝ] F)) (hg : ∀ x, HasFDerivAt f (g x) x) :
    fderiv ℝ (heatFlow a t f) = heatFlow a t g := by
  funext x
  exact (hasFDerivAt_heatFlow_of_hasFDerivAt a t f g hg x).fderiv

/-- Gaussian smoothing is spatially continuously differentiable to every finite order. -/
theorem contDiff_nat_heatFlow (k : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) : ContDiff ℝ k (heatFlow a t f) := by
  induction k generalizing t f with
  | zero => exact contDiff_zero.mpr (heatFlowBUC a t f).continuous
  | succ k ih =>
    have hhalf : 0 < t / 2 := by positivity
    let v := heatFlowBUC a (t / 2) f
    let g := heatFDerivBUC ha hhalf f
    have hg : ∀ x, HasFDerivAt v (g x) x := fun x => hasFDerivAt_heatFlow ha hhalf f x
    have hsplit : heatFlow a t f = heatFlow a (t / 2) v := by
      have hcoe : (v : E → F) = heatFlow a (t / 2) f := funext (heatFlowBUC_apply _ _ f)
      rw [hcoe, heatFlow_add_time ha.le hhalf.le hhalf.le f.uniformContinuous f.norm_apply_le,
        add_halves]
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_heatFlow ha ht f x).differentiableAt, by simp, ?_⟩
    intro w
    rw [hsplit, fderiv_heatFlow_of_hasFDerivAt a (t / 2) v g hg]
    let gw := BUC.postcompCLM (ContinuousLinearMap.apply ℝ F w) g
    have heq : (fun x => heatFlow a (t / 2) g x w) = heatFlow a (t / 2) gw := by
      funext x
      exact ContinuousLinearMap.integral_apply
        (integrable_comp_add_heatScale g.continuous ‖g‖ g.norm_apply_le x) w
    rw [heq]
    exact ih hhalf gw

end

end Planarwave
