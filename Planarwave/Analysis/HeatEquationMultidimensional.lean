/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSmoothMultidimensional
public import Planarwave.Analysis.HeatEquationReal

@[expose] public section

/-!
# The heat equation in finite dimension

For data with a BUC derivative, differentiation of the Gaussian scale gives the trace of the
spatial Hessian. A fixed positive-time semigroup splitting removes the regularity assumption
on the initial data. All results allow Banach-valued data and dimension zero.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff RealInnerProductSpace Laplacian

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Differentiate Gaussian averaging in its spatial scale for BUC differentiable data. -/
theorem hasDerivAt_gaussianAverage_scale (s : ℝ) (f : BUC E F)
    (g : BUC E (E →L[ℝ] F)) (hg : ∀ x, HasFDerivAt f (g x) x) (x : E) :
    HasDerivAt (fun r : ℝ => ∫ z : E, f (x + r • z) ∂stdGaussian E)
      (∫ z : E, g (x + s • z) z ∂stdGaussian E) s := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r z => f (x + r • z)) (F' := fun r z => g (x + r • z) z)
    (bound := fun z : E => ‖g‖ * ‖z‖) (s := univ) (μ := stdGaussian E)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun r => (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    ((integrable_const ‖f‖).mono' (f.continuous.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun z => f.norm_apply_le _))
    (((g.continuous.comp (by fun_prop)).clm_apply continuous_id).aestronglyMeasurable)
    (ae_of_all _ fun z r _ => (g (x + r • z)).le_opNorm z |>.trans
      (mul_le_mul_of_nonneg_right (g.norm_apply_le _) (norm_nonneg _)))
    ((IsGaussian.integrable_id : Integrable (id : E → E) (stdGaussian E)).norm.const_mul ‖g‖)
    (ae_of_all _ fun z r _ => by
      simpa [Function.comp_def] using (hg (x + r • z)).comp_hasDerivAt r
        (((hasDerivAt_id r).smul_const z).const_add x))).2

/-- The trace of the first Hermite kernel applied to the derivative datum. -/
theorem laplacian_heatFlow_of_hasFDerivAt {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (g : BUC E (E →L[ℝ] F)) (hg : ∀ x, HasFDerivAt f (g x) x) (x : E) :
    Δ (heatFlow a t f) x =
      ∫ z : E, (1 / heatScale a t) • g (x + heatScale a t • z) z ∂stdGaussian E := by
  let b := stdOrthonormalBasis ℝ E
  let s := heatScale a t
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply]
  rw [fderiv_heatFlow_of_hasFDerivAt a t f g hg, (hasFDerivAt_heatFlow ha ht g x).fderiv]
  simp_rw [gaussianGradientKernel_apply]
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z : E => (⟪z, b i⟫ / s) • g (x + s • z)) (stdGaussian E) := by
    have h := (integrable_gaussianGradientKernel s g x).apply_continuousLinearMap (b i)
    refine h.congr (ae_of_all _ fun z => ?_)
    simp [innerSL_apply_apply, div_eq_mul_inv, mul_comm]
  change (∑ i, (∫ z : E, (⟪z, b i⟫ / s) • g (x + s • z) ∂stdGaussian E) (b i)) = _
  simp_rw [ContinuousLinearMap.integral_apply (hi _) (b _)]
  rw [← integral_finsetSum _ (fun i _ => (hi i).apply_continuousLinearMap (b i))]
  apply integral_congr_ae
  filter_upwards with z
  have hsum : (∑ i, ⟪z, b i⟫ • b i) = z := by
    simpa only [real_inner_comm z] using b.sum_repr' z
  simp only [smul_apply, div_eq_mul_inv, mul_comm _ s⁻¹,
    mul_smul, ← Finset.smul_sum, ← map_smul, ← map_sum]
  rw [hsum]
  simp only [s, one_smul]

/-- The classical heat equation for initial data with a BUC Fréchet derivative. -/
theorem hasDerivAt_heatFlow_time_of_hasFDerivAt {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (g : BUC E (E →L[ℝ] F)) (hg : ∀ x, HasFDerivAt f (g x) x) (x : E) :
    HasDerivAt (fun r => heatFlow a r f x) (a • Δ (heatFlow a t f) x) t := by
  have h := (hasDerivAt_gaussianAverage_scale (heatScale a t) f g hg x).scomp t
    (hasDerivAt_heatScale ha ht)
  have hcoef : (a / heatScale a t) •
      (∫ z : E, g (x + heatScale a t • z) z ∂stdGaussian E) =
      a • Δ (heatFlow a t f) x := by
    rw [laplacian_heatFlow_of_hasFDerivAt ha ht f g hg x, integral_smul, smul_smul]
    congr 1
    ring
  rw [hcoef] at h
  exact h

/-- The classical heat equation at every positive time for arbitrary finite-dimensional BUC
initial data. -/
theorem hasDerivAt_heatFlow_time {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (x : E) :
    HasDerivAt (fun r => heatFlow a r f x) (a • Δ (heatFlow a t f) x) t := by
  have hhalf : 0 < t / 2 := by positivity
  let v := heatFlowBUC a (t / 2) f
  let g := heatFDerivBUC ha hhalf f
  have hg : ∀ y, HasFDerivAt v (g y) y := fun y => hasFDerivAt_heatFlow ha hhalf f y
  have h := (hasDerivAt_heatFlow_time_of_hasFDerivAt ha
    (show 0 < t - t / 2 by linarith) v g hg x).scomp t
      ((hasDerivAt_id t).sub_const (t / 2))
  simp only [one_smul, Function.comp_def] at h
  have hsplit (r : ℝ) (hr : t / 2 < r) :
      heatFlow a (r - t / 2) v = heatFlow a r f := by
    have hcoe : (v : E → F) = heatFlow a (t / 2) f := funext (heatFlowBUC_apply _ _ f)
    rw [hcoe, heatFlow_add_time ha.le (sub_pos.mpr hr).le hhalf.le
      f.uniformContinuous f.norm_apply_le, sub_add_cancel]
  rw [hsplit t (by linarith)] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with r hr
  exact congrFun (hsplit r hr).symm x

end

end Planarwave
