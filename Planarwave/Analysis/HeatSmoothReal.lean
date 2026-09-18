/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSmoothing

@[expose] public section

/-!
# Smoothness of one-dimensional heat flow

The first derivative of a positive-time heat orbit is itself BUC. Differentiation commutes with
heat flow on data with a bounded continuous derivative. Splitting the time interval and iterating
these two facts upgrades the existing second-order smoothing theorem to every finite order.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The first derivative of a positive-time heat orbit is uniformly continuous, since its
derivative has a global bound. -/
theorem uniformContinuous_deriv_heatFlow_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) : UniformContinuous (deriv (heatFlow a t f)) := by
  have hd : Differentiable ℝ (deriv (heatFlow a t f)) := by
    rw [deriv_heatFlow_real ha ht f]
    exact fun x => (hasDerivAt_gaussianSmoothD1 _ (heatScale_pos_of_pos ha ht) f x).differentiableAt
  apply (lipschitzWith_of_nnnorm_deriv_le (C := ⟨‖f‖ / (a * t), by positivity⟩) hd ?_).uniformContinuous
  intro x
  exact norm_second_deriv_heatFlow_real_le ha ht f x

/-- The spatial derivative of the heat orbit as bounded uniformly continuous data. -/
def heatDerivBUC {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC ℝ F) : BUC ℝ F where
  toBCF :=
    { toFun := deriv (heatFlow a t f)
      continuous_toFun := (uniformContinuous_deriv_heatFlow_real ha ht f).continuous
      map_bounded' := by
        refine ⟨2 * (‖f‖ / heatScale a t), ?_⟩
        intro x y
        calc
          dist (deriv (heatFlow a t f) x) (deriv (heatFlow a t f) y) ≤
              ‖deriv (heatFlow a t f) x‖ + ‖deriv (heatFlow a t f) y‖ :=
            by rw [dist_eq_norm]; exact norm_sub_le _ _
          _ ≤ ‖f‖ / heatScale a t + ‖f‖ / heatScale a t :=
            add_le_add (norm_deriv_heatFlow_real_le ha ht f x)
              (norm_deriv_heatFlow_real_le ha ht f y)
          _ = 2 * (‖f‖ / heatScale a t) := by ring }
  uniformContinuous' := uniformContinuous_deriv_heatFlow_real ha ht f

@[simp]
theorem heatDerivBUC_apply {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) (x : ℝ) : heatDerivBUC ha ht f x = deriv (heatFlow a t f) x := rfl

/-- Passing one spatial derivative through Gaussian averaging when the derivative is BUC. -/
theorem hasDerivAt_heatFlow_of_hasDerivAt (a t : ℝ) (f g : BUC ℝ F)
    (hg : ∀ x, HasDerivAt f (g x) x) (x : ℝ) :
    HasDerivAt (heatFlow a t f) (heatFlow a t g x) x := by
  let s := heatScale a t
  have hd : ∀ z x : ℝ, HasDerivAt (fun y => f (y + s * z)) (g (x + s * z)) x := by
    intro z x
    simpa [Function.comp_def] using
      (hg (x + s * z)).scomp x ((hasDerivAt_id x).add_const (s * z))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x z : ℝ => f (x + s * z))
    (F' := fun x z : ℝ => g (x + s * z))
    (bound := fun _ : ℝ => ‖g‖) (s := univ) (μ := stdGaussian ℝ)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x => (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_add_heatScale f.continuous ‖f‖ f.norm_apply_le x)
    ((g.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun z x _ => g.norm_apply_le (x + s * z))
    (integrable_const ‖g‖)
    (ae_of_all _ fun z x _ => hd z x)).2

/-- Spatial differentiation commutes with heat averaging on BUC data with BUC derivative. -/
theorem deriv_heatFlow_of_hasDerivAt (a t : ℝ) (f g : BUC ℝ F)
    (hg : ∀ x, HasDerivAt f (g x) x) :
    deriv (heatFlow a t f) = heatFlow a t g := by
  funext x
  exact (hasDerivAt_heatFlow_of_hasDerivAt a t f g hg x).deriv

/-- Gaussian smoothing is continuously differentiable to every finite order. -/
theorem contDiff_nat_heatFlow_real (k : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) : ContDiff ℝ k (heatFlow a t f) := by
  induction k generalizing t f with
  | zero => exact contDiff_zero.mpr (heatFlowBUC a t f).continuous
  | succ k ih =>
    have hhalf : 0 < t / 2 := by positivity
    have hsplit : heatFlow a t f = heatFlow a (t / 2) (heatFlowBUC a (t / 2) f) := by
      have h := heatFlow_add_time ha.le hhalf.le hhalf.le f.uniformContinuous f.norm_apply_le
      have hcoe : (heatFlowBUC a (t / 2) f : ℝ → F) = heatFlow a (t / 2) f :=
        funext (heatFlowBUC_apply _ _ f)
      rw [hcoe]
      simpa only [add_halves] using h.symm
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨(contDiff_two_heatFlow_real ha ht f).differentiable (by norm_num), by simp, ?_⟩
    rw [hsplit, deriv_heatFlow_of_hasDerivAt a (t / 2)
      (heatFlowBUC a (t / 2) f) (heatDerivBUC ha hhalf f)
      (fun x => ((contDiff_two_heatFlow_real ha hhalf f).differentiable
        (by norm_num) x).hasDerivAt)]
    exact ih hhalf (heatDerivBUC ha hhalf f)

/-- Positive-time heat flow of BUC data is smooth in the spatial variable. -/
theorem contDiff_infty_heatFlow_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) : ContDiff ℝ ∞ (heatFlow a t f) :=
  contDiff_infty.mpr fun k => contDiff_nat_heatFlow_real k ha ht f

end

end Planarwave
