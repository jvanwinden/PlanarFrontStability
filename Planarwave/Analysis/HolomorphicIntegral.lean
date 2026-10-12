/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Holomorphic parameter integrals with local norm bounds

The complex-time Volterra series involves operator-valued integrands which need not
be norm continuous at the integration endpoints. Cauchy's estimate and dominated
differentiation allow us to use almost-everywhere analyticity and local norm bounds.
-/

open Filter MeasureTheory Metric Set Topology

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Cauchy's derivative estimate on the inner half of a disk. -/
theorem norm_deriv_le_of_bounded_ball {f : ℂ → F} {x z : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball x (2 * r)))
    (hb : ∀ w ∈ ball x (2 * r), ‖f w‖ ≤ M) (hz : z ∈ ball x r) :
    ‖deriv f z‖ ≤ M / r := by
  have hsub : closedBall z r ⊆ ball x (2 * r) := by
    intro w hw
    apply mem_ball.mpr
    exact (dist_triangle w z x).trans_lt (by linarith [mem_closedBall.mp hw, mem_ball.mp hz])
  rw [← Complex.cderiv_eq_deriv isOpen_ball hf.differentiableOn hr hsub]
  exact Complex.norm_cderiv_le hr (fun w hw ↦ hb w (hsub (sphere_subset_closedBall hw)))

omit [CompleteSpace F] in
/-- The parameter derivative is strongly measurable, as the almost-everywhere
limit of measurable difference quotients in a fixed disk. -/
theorem aestronglyMeasurable_deriv_of_ball
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℂ → α → F} {x : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hmeas : ∀ z ∈ ball x (2 * r), AEStronglyMeasurable (f z) μ)
    (hderiv : ∀ᵐ a ∂μ, DifferentiableAt ℂ (fun z ↦ f z a) x) :
    AEStronglyMeasurable (fun a ↦ deriv (fun z ↦ f z a) x) μ := by
  let d (n : ℕ) : ℝ := r / (n + 1)
  have hdpos (n) : 0 < d n := by dsimp [d]; positivity
  have hdle (n) : d n ≤ r := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [show 0 ≤ (n : ℝ) by positivity]
  have hmem (n) : x + (d n : ℂ) ∈ ball x (2 * r) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hdpos n)]
    linarith [hdle n]
  have hdlim : Tendsto (fun n ↦ (d n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    apply Complex.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [d, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n ↦ x + (d n : ℂ)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [add_zero] using hdlim.const_add x, Eventually.of_forall ?_⟩
    intro n
    simpa only [mem_compl_iff, mem_singleton_iff, add_eq_left, Complex.ofReal_eq_zero] using (hdpos n).ne'
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n a ↦ slope (fun z ↦ f z a) x (x + (d n : ℂ)))
  · intro n
    exact ((hmeas _ (hmem n)).sub (hmeas x (mem_ball_self (by positivity)))).const_smul _
  · filter_upwards [hderiv] with a ha
    exact (hasDerivAt_iff_tendsto_slope.mp ha.hasDerivAt).comp hlim

/-- A uniformly locally bounded holomorphic family can be integrated over a finite
measure space. Measurability and analyticity are only required almost everywhere. -/
theorem analyticOnNhd_integral_of_locally_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℂ → α → F} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ᵐ a ∂μ, AnalyticOnNhd ℂ (fun z ↦ f z a) U)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (f z) μ)
    (hbound : ∀ x ∈ U, ∃ r > 0, ball x (2 * r) ⊆ U ∧ ∃ M : ℝ,
      ∀ᵐ a ∂μ, ∀ z ∈ ball x (2 * r), ‖f z a‖ ≤ M) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ a, f z a ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro x hx
  obtain ⟨r, hr, hsub, M, hb⟩ := hbound x hx
  have hxball : x ∈ ball x (2 * r) := mem_ball_self (by positivity)
  have hmeas' : ∀ z ∈ ball x (2 * r), AEStronglyMeasurable (f z) μ :=
    fun z hz ↦ hmeas z (hsub hz)
  have hderiv : ∀ᵐ a ∂μ, DifferentiableAt ℂ (fun z ↦ f z a) x :=
    hf.mono fun a ha ↦ (ha x hx).differentiableAt
  have hint : Integrable (f x) μ := (integrable_const M).mono' (hmeas x hx)
    (hb.mono fun a ha ↦ ha x hxball)
  have hdiff : ∀ᵐ a ∂μ, ∀ z ∈ ball x r, HasDerivAt (fun z ↦ f z a)
      (deriv (fun z ↦ f z a) z) z := by
    filter_upwards [hf] with a ha z hz
    exact (ha z (hsub (ball_subset_ball (by linarith) hz))).differentiableAt.hasDerivAt
  have hdbound : ∀ᵐ a ∂μ, ∀ z ∈ ball x r, ‖deriv (fun z ↦ f z a) z‖ ≤ M / r := by
    filter_upwards [hf, hb] with a ha hb z hz
    exact norm_deriv_le_of_bounded_ball hr (ha.mono hsub) hb hz
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds x hr)
    (Filter.eventually_of_mem (ball_mem_nhds x (by positivity : 0 < 2 * r)) hmeas')
    hint (aestronglyMeasurable_deriv_of_ball hr hmeas' hderiv) hdbound (integrable_const (M / r)) hdiff
  exact h.2.differentiableAt.differentiableWithinAt

end

end Planarwave
