/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSmoothReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The one-dimensional heat equation

First differentiate Gaussian averaging with respect to its scale on data with a bounded
continuous derivative. The first Hermite-kernel identity turns this into the heat equation.
For arbitrary BUC data, split off a fixed positive time interval before differentiating.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Differentiation of the spatial scale of Gaussian averaging. -/
theorem hasDerivAt_gaussianSmooth_scale (s x : ℝ) (f g : BUC ℝ F)
    (hg : ∀ x, HasDerivAt f (g x) x) :
    HasDerivAt (fun r => gaussianSmooth r f x)
      (∫ z : ℝ, z • g (x + s * z) ∂stdGaussian ℝ) s := by
  have hint : Integrable (fun z : ℝ => f (x + s * z)) (stdGaussian ℝ) :=
    (integrable_const ‖f‖).mono' (f.continuous.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun z => f.norm_apply_le _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r z : ℝ => f (x + r * z))
    (F' := fun r z : ℝ => z • g (x + r * z))
    (bound := fun z : ℝ => |z| * ‖g‖) (s := univ) (μ := stdGaussian ℝ)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun r => (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    hint
    ((continuous_id.smul (g.continuous.comp (by fun_prop))).aestronglyMeasurable)
    (ae_of_all _ fun z r _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (g.norm_apply_le _) (abs_nonneg _))
    (integrable_abs_stdGaussian.mul_const ‖g‖)
    (ae_of_all _ fun z r _ => by
      simpa [Function.comp_def] using
        (hg (x + r * z)).scomp r (((hasDerivAt_id r).mul_const z).const_add x))).2

/-- Derivative of the positive-time Gaussian scale. -/
theorem hasDerivAt_heatScale {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (heatScale a) (a / heatScale a t) t := by
  have hscale : 2 * a * t ≠ 0 := ne_of_gt (mul_pos (mul_pos (by norm_num) ha) ht)
  have h := ((hasDerivAt_id t).const_mul (2 * a)).sqrt (by simpa only [id_eq] using hscale)
  have heq : heatScale a = fun r => Real.sqrt (2 * a * r) := by
    funext r
    rw [heatScale]
  rw [heq]
  simpa only [heatScale, id_eq, mul_one,
    mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)] using h

/-- The heat equation on initial data with bounded uniformly continuous derivative. -/
theorem hasDerivAt_heatFlow_time_of_hasDerivAt {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f g : BUC ℝ F) (hg : ∀ x, HasDerivAt f (g x) x) (x : ℝ) :
    HasDerivAt (fun r => heatFlow a r f x)
      (a • deriv (deriv (heatFlow a t f)) x) t := by
  have h := (hasDerivAt_gaussianSmooth_scale (heatScale a t) x f g hg).scomp t
    (hasDerivAt_heatScale ha ht)
  have hcoef : (a / heatScale a t) •
      (∫ z : ℝ, z • g (x + heatScale a t * z) ∂stdGaussian ℝ) =
      a • deriv (deriv (heatFlow a t f)) x := by
    rw [deriv_heatFlow_of_hasDerivAt a t f g hg, deriv_heatFlow_real ha ht g,
      gaussianSmoothD1, ← integral_smul, ← integral_smul]
    apply integral_congr_ae
    filter_upwards with z
    simp only [smul_smul]
    congr 1
    ring
  rw [hcoef] at h
  simpa only [Function.comp_def, heatFlow_real_eq_gaussianSmooth] using h

/-- The classical heat equation holds at every positive time for arbitrary BUC initial data. -/
theorem hasDerivAt_heatFlow_time_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) (x : ℝ) :
    HasDerivAt (fun r => heatFlow a r f x)
      (a • deriv (deriv (heatFlow a t f)) x) t := by
  have hhalf : 0 < t / 2 := by positivity
  let v := heatFlowBUC a (t / 2) f
  let g := heatDerivBUC ha hhalf f
  have hg : ∀ y, HasDerivAt v (g y) y :=
    fun y => ((contDiff_two_heatFlow_real ha hhalf f).differentiable (by norm_num) y).hasDerivAt
  have hshift : 0 < t - t / 2 := by linarith
  have h := (hasDerivAt_heatFlow_time_of_hasDerivAt ha hshift v g hg x).scomp t
    ((hasDerivAt_id t).sub_const (t / 2))
  simp only [one_smul, Function.comp_def] at h
  have hsplit (r : ℝ) (hr : t / 2 < r) :
      heatFlow a (r - t / 2) v = heatFlow a r f := by
    have hcoe : (v : ℝ → F) = heatFlow a (t / 2) f :=
      funext (heatFlowBUC_apply _ _ f)
    rw [hcoe, heatFlow_add_time ha.le (sub_pos.mpr hr).le hhalf.le
      f.uniformContinuous f.norm_apply_le, sub_add_cancel]
  rw [hsplit t (by linarith)] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with r hr
  exact congrFun (hsplit r hr).symm x

end

end Planarwave
