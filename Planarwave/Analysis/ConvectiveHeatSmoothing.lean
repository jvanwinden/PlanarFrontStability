/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ConvectiveHeatGenerator

@[expose] public section

/-!
# Quantitative smoothing for convective heat flow

The diagonal heat calculation underlying the sectoriality assertion in Section 2 gives
the short-time generator bound `t ‖A S(t)‖ ≤ C`. The constant below is uniform over
nonnegative Fourier damping parameters and diffusion rates bounded below by `μ > 0`.
-/

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Translation leaves the first heat-kernel derivative bound unchanged. -/
theorem norm_convectiveHeatFlow_derivative_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (c : ℝ) (f g : BUC ℝ F)
    (hg : ∀ x, HasDerivAt (convectiveHeatFlowBUC a t c f) (g x) x) :
    ‖g‖ ≤ ‖f‖ / heatScale a t := by
  apply (BUC.norm_le (div_nonneg (norm_nonneg _) (heatScale_pos_of_pos ha ht).le)).mpr
  intro x
  have hd := (((contDiff_two_heatFlow_real ha ht f).differentiable (by norm_num))
    (x + t * c)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const (t * c))
  have hd' : HasDerivAt (convectiveHeatFlowBUC a t c f)
      (deriv (heatFlow a t f) (x + t * c)) x := by
    change HasDerivAt (fun y ↦ convectiveHeatFlowBUC a t c f y) _ x
    simpa only [Function.comp_def, id_eq, one_smul, convectiveHeatFlowBUC_apply] using! hd
  rw [(hg x).unique hd']
  exact norm_deriv_heatFlow_real_le ha ht f _

/-- The second derivative has the usual inverse-time heat bound, also in BUC norm. -/
theorem norm_convectiveHeatFlow_second_derivative_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (c : ℝ) (f g h : BUC ℝ F)
    (hg : ∀ x, HasDerivAt (convectiveHeatFlowBUC a t c f) (g x) x)
    (hh : ∀ x, HasDerivAt g (h x) x) :
    ‖h‖ ≤ ‖f‖ / (a * t) := by
  have heq : (g : ℝ → F) = fun x ↦ deriv (heatFlow a t f) (x + t * c) := by
    funext x
    have hd := (((contDiff_two_heatFlow_real ha ht f).differentiable (by norm_num))
      (x + t * c)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const (t * c))
    apply (hg x).unique
    change HasDerivAt (fun y ↦ convectiveHeatFlowBUC a t c f y) _ x
    simpa only [Function.comp_def, id_eq, one_smul, convectiveHeatFlowBUC_apply] using! hd
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  have hd : HasDerivAt (deriv (heatFlow a t f))
      (deriv (deriv (heatFlow a t f)) (x + t * c)) (x + t * c) := by
    rw [deriv_heatFlow_real ha ht f]
    exact (hasDerivAt_gaussianSmoothD1 _ (heatScale_pos_of_pos ha ht) f _).differentiableAt.hasDerivAt
  have hd' := hd.scomp x ((hasDerivAt_id x).add_const (t * c))
  have hh' := hh x
  rw [heq] at hh'
  rw [hh'.unique (by simpa only [Function.comp_def, one_smul] using! hd')]
  exact norm_second_deriv_heatFlow_real_le ha ht f _

/-- For short times the first derivative costs at most `1 / (sqrt (2 μ) t)`.
This deliberately weaker form combines with the second derivative in the generator estimate. -/
theorem time_mul_norm_convectiveHeatFlow_derivative_le {a μ t : ℝ}
    (hμ : 0 < μ) (hμa : μ ≤ a) (ht : 0 < t) (ht₁ : t ≤ 1)
    (c : ℝ) (f g : BUC ℝ F)
    (hg : ∀ x, HasDerivAt (convectiveHeatFlowBUC a t c f) (g x) x) :
    t * ‖g‖ ≤ ‖f‖ / Real.sqrt (2 * μ) := by
  have ha := hμ.trans_le hμa
  have hs := heatScale_pos_of_pos ha ht
  have hμs : 0 < Real.sqrt (2 * μ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : Real.sqrt (2 * μ) * t ≤ heatScale a t := by
    have heq := heatScale_sq ha.le ht.le
    have hsμ := Real.sq_sqrt (show 0 ≤ 2 * μ by positivity)
    have htt : t * t ≤ t := by nlinarith
    have hm := mul_le_mul_of_nonneg_left htt (show 0 ≤ 2 * μ by positivity)
    have hma := mul_le_mul_of_nonneg_right hμa ht.le
    nlinarith [sq_nonneg (Real.sqrt (2 * μ) * t - heatScale a t)]
  have hg' := (le_div_iff₀ hs).mp (norm_convectiveHeatFlow_derivative_le ha ht c f g hg)
  apply (le_div_iff₀ hμs).mpr
  calc
    t * ‖g‖ * Real.sqrt (2 * μ) = ‖g‖ * (Real.sqrt (2 * μ) * t) := by ring
    _ ≤ ‖g‖ * heatScale a t := mul_le_mul_of_nonneg_left hscale (norm_nonneg _)
    _ ≤ ‖f‖ := hg'

/-- The Fourier damping absorbs its own generator factor. -/
theorem mul_exp_neg_le_one (r : ℝ) :
    r * Real.exp (-r) ≤ 1 := by
  have h : r ≤ Real.exp r := le_trans (by linarith) (Real.add_one_le_exp r)
  calc
    r * Real.exp (-r) ≤ Real.exp r * Real.exp (-r) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The complete damped scalar generator has a `1/t` bound uniform in `q ≥ 0`.
The three terms are estimated separately, as in the diagonal heat calculation. -/
theorem time_mul_norm_dampedConvectiveHeat_generator_le {a μ t q : ℝ}
    (hμ : 0 < μ) (hμa : μ ≤ a) (ht : 0 < t) (ht₁ : t ≤ 1) (hq : 0 ≤ q)
    (c : ℝ) (f g h : BUC ℝ F)
    (hg : ∀ x, HasDerivAt (convectiveHeatFlowBUC a t c f) (g x) x)
    (hh : ∀ x, HasDerivAt g (h x) x) :
    t * ‖Real.exp ((-q * a) * t) •
      (a • h + c • g - (q * a) • convectiveHeatFlowBUC a t c f)‖ ≤
      (2 + |c| / Real.sqrt (2 * μ)) * ‖f‖ := by
  have ha := hμ.trans_le hμa
  let r := Real.exp ((-q * a) * t)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr₁ : r ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) ha.le) ht.le)
  have hsecond : t * a * ‖h‖ ≤ ‖f‖ := by
    have hb := (le_div_iff₀ (mul_pos ha ht)).mp
      (norm_convectiveHeatFlow_second_derivative_le ha ht c f g h hg hh)
    nlinarith
  have hfirst := time_mul_norm_convectiveHeatFlow_derivative_le hμ hμa ht ht₁ c f g hg
  have hdamp : t * (q * a) * r ≤ 1 := by
    have heq : (-q * a) * t = -(q * a * t) := by ring
    dsimp only [r]
    rw [heq]
    nlinarith [mul_exp_neg_le_one (q * a * t)]
  have hheat : ‖convectiveHeatFlowBUC a t c f‖ ≤ ‖f‖ := norm_convectiveHeatFlowBUC_le a t c f
  have hnorm : ‖a • h + c • g - (q * a) • convectiveHeatFlowBUC a t c f‖ ≤
      a * ‖h‖ + |c| * ‖g‖ + (q * a) * ‖f‖ := by
    calc
      _ ≤ ‖a • h‖ + ‖c • g‖ + ‖(q * a) • convectiveHeatFlowBUC a t c f‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ a * ‖h‖ + |c| * ‖g‖ + (q * a) * ‖f‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.le,
          abs_of_nonneg (show 0 ≤ q * a by positivity)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hheat
          (show 0 ≤ q * a by positivity))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  change t * (r * _) ≤ _
  calc
    _ ≤ t * (r * (a * ‖h‖ + |c| * ‖g‖ + (q * a) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm hr) ht.le
    _ = r * (t * a * ‖h‖) + r * |c| * (t * ‖g‖) +
        (t * (q * a) * r) * ‖f‖ := by ring
    _ ≤ 1 * ‖f‖ + (1 * |c|) * (‖f‖ / Real.sqrt (2 * μ)) + 1 * ‖f‖ := by
      exact add_le_add (add_le_add (mul_le_mul hr₁ hsecond (by positivity) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_right hr₁ (abs_nonneg c)) hfirst
          (by positivity) (by positivity)))
        (mul_le_mul_of_nonneg_right hdamp (norm_nonneg _))
    _ = _ := by ring

end

end Planarwave
