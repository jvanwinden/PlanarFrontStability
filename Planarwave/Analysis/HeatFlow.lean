/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.IntegralConvolution

@[expose] public section

/-!
# The Gaussian heat flow on a finite-dimensional Euclidean space

This file starts the analytic infrastructure used in the proof of the effective-front theorem.
We realize the heat flow probabilistically: at time `t`, with diffusivity `a`, one averages a
function over a centred Gaussian displacement of standard deviation `sqrt (2 * a * t)`.

The definition is made for functions with values in an arbitrary real Banach space.  The lemmas
below establish the zero-time identity, linearity, preservation of constants, and the sharp
supremum-norm contraction.  Later files add the semigroup, smoothing, and heat-equation
properties needed for the Cole--Hopf argument.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Planarwave

section HeatFlow

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The spatial standard deviation in the heat flow with diffusivity `a` at time `t`. -/
noncomputable def heatScale (a t : ℝ) : ℝ := Real.sqrt (2 * a * t)

theorem continuous_heatScale (a : ℝ) : Continuous (heatScale a) := by
  unfold heatScale
  fun_prop

theorem tendsto_heatScale_zero (a : ℝ) :
    Tendsto (heatScale a) (nhds 0) (nhds 0) := by
  convert (continuous_heatScale a).tendsto 0 using 1
  simp [heatScale]

/-- The centred Gaussian heat measure with covariance `2 * a * t`. -/
noncomputable def heatMeasure (a t : ℝ) : Measure E :=
  (stdGaussian E).map (heatScale a t • ·)

noncomputable instance (a t : ℝ) : IsProbabilityMeasure (heatMeasure (E := E) a t) := by
  unfold heatMeasure
  infer_instance

/-- Gaussian realization of the heat flow `exp (t * a * Δ)`.

For the PDE applications we use this only when `0 ≤ a` and `0 ≤ t`.  Keeping the definition
total is convenient in Lean; the mathematical properties state the required sign hypotheses.
-/
noncomputable def heatFlow (a t : ℝ) (f : E → F) (x : E) : F :=
  ∫ z, f (x + heatScale a t • z) ∂(stdGaussian E)

theorem heatFlow_eq_integral_heatMeasure (a t : ℝ) (f : E → F) (hf : Continuous f) (x : E) :
    heatFlow a t f x = ∫ z, f (x + z) ∂(heatMeasure (E := E) a t) := by
  rw [heatFlow, heatMeasure, integral_map (by fun_prop) (by fun_prop)]

@[simp]
theorem heatScale_zero_right (a : ℝ) : heatScale a 0 = 0 := by
  simp [heatScale]

@[simp]
theorem heatScale_zero_left (t : ℝ) : heatScale 0 t = 0 := by
  simp [heatScale]

theorem heatScale_sq {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    heatScale a t ^ 2 = 2 * a * t := by
  rw [heatScale, Real.sq_sqrt]
  positivity

theorem charFun_heatMeasure {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (w : E) :
    charFun (heatMeasure (E := E) a t) w = Complex.exp (-(a * t * ‖w‖ ^ 2)) := by
  rw [heatMeasure, charFun_map_smul, charFun_stdGaussian]
  simp only [norm_smul, Real.norm_eq_abs]
  push_cast
  congr 1
  norm_cast
  rw [mul_pow, sq_abs, heatScale_sq ha ht]
  ring

/-- Addition of independent heat displacements adds their times. -/
theorem heatMeasure_conv {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatMeasure (E := E) a s ∗ heatMeasure (E := E) a t = heatMeasure (E := E) a (s + t) := by
  apply Measure.ext_of_charFun
  funext w
  rw [charFun_conv, charFun_heatMeasure ha hs, charFun_heatMeasure ha ht,
    charFun_heatMeasure ha (add_nonneg hs ht), ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp]
theorem heatFlow_zero (a : ℝ) (f : E → F) (x : E) : heatFlow a 0 f x = f x := by
  simp [heatFlow]

@[simp]
theorem heatFlow_const (a t : ℝ) (c : F) : heatFlow a t (fun _ : E => c) = fun _ => c := by
  funext x
  simp [heatFlow]

/-- A bounded continuous integrand is integrable against the standard Gaussian probability
measure. -/
theorem integrable_comp_add_heatScale {a t : ℝ} {f : E → F} (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    Integrable (fun z => f (x + heatScale a t • z)) (stdGaussian E) := by
  refine Integrable.mono' (integrable_const C) (hf.comp_aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with z
  simpa using hC (x + heatScale a t • z)

theorem integrable_comp_add_heatMeasure {a t : ℝ} {f : E → F} (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    Integrable (fun z => f (x + z)) (heatMeasure (E := E) a t) := by
  refine Integrable.mono' (integrable_const C) (hf.comp_aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with z
  exact hC _

theorem heatFlow_add_of_bounded_continuous (a t : ℝ) {f g : E → F}
    (hf : Continuous f) (hg : Continuous g)
    (Cf Cg : ℝ) (hCf : ∀ x, ‖f x‖ ≤ Cf) (hCg : ∀ x, ‖g x‖ ≤ Cg) :
    heatFlow a t (fun x => f x + g x) = fun x => heatFlow a t f x + heatFlow a t g x := by
  funext x
  simp only [heatFlow]
  rw [integral_add (integrable_comp_add_heatScale hf Cf hCf x)
    (integrable_comp_add_heatScale hg Cg hCg x)]

theorem heatFlow_smul (a t r : ℝ) (f : E → F) :
    heatFlow a t (fun x => r • f x) = fun x => r • heatFlow a t f x := by
  funext x
  change (∫ z, r • f (x + heatScale a t • z) ∂(stdGaussian E)) =
    r • ∫ z, f (x + heatScale a t • z) ∂(stdGaussian E)
  rw [integral_smul]

/-- The Gaussian heat flow is a contraction in the supremum norm. -/
theorem norm_heatFlow_le {a t C : ℝ} {f : E → F} (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    ‖heatFlow a t f x‖ ≤ C := by
  calc
    ‖heatFlow a t f x‖ ≤ C * (stdGaussian E).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with z
      exact hC _
    _ = C := by simp

theorem dist_heatFlow_le {a t C Cf Cg : ℝ} {f g : E → F}
    (hf : Continuous f) (hg : Continuous g)
    (hCf : ∀ x, ‖f x‖ ≤ Cf) (hCg : ∀ x, ‖g x‖ ≤ Cg)
    (hC : ∀ x, dist (f x) (g x) ≤ C) (x : E) :
    dist (heatFlow a t f x) (heatFlow a t g x) ≤ C := by
  rw [dist_eq_norm]
  change ‖(∫ z, f (x + heatScale a t • z) ∂(stdGaussian E)) -
    ∫ z, g (x + heatScale a t • z) ∂(stdGaussian E)‖ ≤ C
  rw [← integral_sub (integrable_comp_add_heatScale hf Cf hCf x)
    (integrable_comp_add_heatScale hg Cg hCg x)]
  exact norm_heatFlow_le (f := fun x => f x - g x)
    (by simpa [dist_eq_norm] using hC) x

/-- Gaussian averaging preserves uniform continuity. -/
theorem uniformContinuous_heatFlow {a t C : ℝ} {f : E → F}
    (hf : UniformContinuous f) (hC : ∀ x, ‖f x‖ ≤ C) :
    UniformContinuous (heatFlow a t f) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  have hpoint : ∀ z : E,
      dist (f (x + heatScale a t • z)) (f (y + heatScale a t • z)) < ε / 2 := by
    intro z
    apply hmod
    simpa only [dist_add_right] using hxy
  rw [dist_eq_norm]
  change ‖(∫ z, f (x + heatScale a t • z) ∂(stdGaussian E)) -
    ∫ z, f (y + heatScale a t • z) ∂(stdGaussian E)‖ < ε
  rw [← integral_sub
    (integrable_comp_add_heatScale hf.continuous C hC x)
    (integrable_comp_add_heatScale hf.continuous C hC y)]
  refine (norm_integral_le_of_norm_le_const
    (μ := stdGaussian E) (C := ε / 2) ?_).trans_lt ?_
  · filter_upwards with z
    simpa [dist_eq_norm] using (hpoint z).le
  · have : ε / 2 < ε := by linarith
    simpa using this

theorem continuous_heatFlow {a t C : ℝ} {f : E → F}
    (hf : UniformContinuous f) (hC : ∀ x, ‖f x‖ ≤ C) :
    Continuous (heatFlow a t f) :=
  (uniformContinuous_heatFlow hf hC).continuous

/-- Semigroup law for the Gaussian heat flow on bounded uniformly continuous functions. -/
theorem heatFlow_add_time {a s t C : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {f : E → F} (hf : UniformContinuous f) (hC : ∀ x, ‖f x‖ ≤ C) :
    heatFlow a s (heatFlow a t f) = heatFlow a (s + t) f := by
  funext x
  rw [heatFlow_eq_integral_heatMeasure a s _ (continuous_heatFlow hf hC) x]
  simp_rw [heatFlow_eq_integral_heatMeasure a t f hf.continuous]
  have hint : Integrable (fun z => f (x + z))
      (heatMeasure (E := E) a s ∗ heatMeasure (E := E) a t) := by
    rw [heatMeasure_conv ha hs ht]
    exact integrable_comp_add_heatMeasure hf.continuous C hC x
  simp_rw [add_assoc]
  rw [← integral_conv hint]
  rw [heatMeasure_conv ha hs ht]
  rw [heatFlow_eq_integral_heatMeasure a (s + t) f hf.continuous x]

/-- At each spatial point, the heat flow converges to the initial value as time tends to zero
from the right.  Uniform convergence for BUC data is proved after bundling the flow in
`HeatSemigroup`. -/
theorem tendsto_heatFlow_zero_apply {a C : ℝ} (_ha : 0 ≤ a) {f : E → F}
    (hf : Continuous f) (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    Tendsto (fun t ↦ heatFlow a t f x) (nhdsWithin 0 (Set.Ici 0)) (nhds (f x)) := by
  have hsqrt : Tendsto (fun t : ℝ ↦ heatScale a t) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
    unfold heatScale
    have harg : Tendsto (fun t : ℝ ↦ 2 * a * t) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
      have ht : Tendsto (fun t : ℝ ↦ t) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℝ ↦ a) (nhdsWithin 0 (Set.Ici 0)) (nhds a))).mul ht
    convert (Real.continuous_sqrt.tendsto 0).comp harg using 1 <;> simp [Function.comp_def]
  have hmeas : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ici 0),
      AEStronglyMeasurable (fun z : E ↦ f (x + heatScale a t • z)) (stdGaussian E) := by
    filter_upwards with t
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ici 0),
      ∀ᵐ z ∂(stdGaussian E), ‖f (x + heatScale a t • z)‖ ≤ C := by
    filter_upwards with t
    filter_upwards with z
    exact hC _
  have hlim : ∀ᵐ z ∂(stdGaussian E),
      Tendsto (fun t ↦ f (x + heatScale a t • z)) (nhdsWithin 0 (Set.Ici 0)) (nhds (f x)) := by
    filter_upwards with z
    exact (hf.tendsto x).comp (by simpa using tendsto_const_nhds.add (hsqrt.smul_const z))
  simpa [heatFlow] using
    (tendsto_integral_filter_of_dominated_convergence (fun _ : E ↦ C) hmeas hbound
      (integrable_const C) hlim)

end HeatFlow

end Planarwave
