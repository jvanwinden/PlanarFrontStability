/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupLaplace
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# The first time moment of the Laplace resolvent

Integrating the derivative of `t T(t) R x` identifies `R²` with the Laplace
transform of `t T(t)`. This provides the absolutely integrable transform used
in differentiated Laplace inversion, without assuming norm continuity at zero.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The first time moment of an exponentially decaying orbit is integrable. -/
theorem integrableOn_time_smul_realOrbit (S : C0Semigroup ℂ E)
    {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    IntegrableOn (fun t : ℝ ↦ t • S.realOrbit x t) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ ↦ t * Real.exp (ω * t)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (b := -ω) (by norm_num) (by norm_num) (neg_pos.mpr hω)
  apply (hi.const_mul (M * ‖x‖)).mono'
    (continuous_id.smul (S.continuous_realOrbit x)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖t • S.realOrbit x t‖ ≤ (M * ‖x‖) * (t * Real.exp (ω * t))
  rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hh := mul_le_mul_of_nonneg_left (S.norm_realOrbit_le_of_exp_bound hbound x ht.le) ht.le
  simpa only [mul_left_comm, mul_comm, mul_assoc] using hh

/-- Polynomial time factors still vanish at infinity under exponential decay. -/
theorem tendsto_time_smul_realOrbit_zero (S : C0Semigroup ℂ E)
    {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    Tendsto (fun t : ℝ ↦ t • S.realOrbit x t) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ ↦ (M * ‖x‖) * (t * Real.exp (ω * t))) atTop (𝓝 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (-ω) (neg_pos.mpr hω)
    simpa using hh.const_mul (M * ‖x‖)
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_smul, Real.norm_of_nonneg ht]
  have hh := mul_le_mul_of_nonneg_left (S.norm_realOrbit_le_of_exp_bound hbound x ht) ht
  simpa only [mul_left_comm, mul_comm, mul_assoc] using hh

/-- Squaring the orbit-integral inverse inserts one time factor. -/
theorem integralRealOrbitCLM_sq_apply (S : C0Semigroup ℂ E)
    {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    (S.integralRealOrbitCLM hω hbound).comp (S.integralRealOrbitCLM hω hbound) x =
      ∫ t in Ioi (0 : ℝ), t • S.realOrbit x t := by
  let u := S.integralRealOrbitCLM hω hbound x
  have hu : S.HasGeneratorAt u (-x) := S.hasGeneratorAt_integral_realOrbit hω hbound x
  have hc : Continuous (fun t : ℝ ↦ t • S.realOrbit u t) :=
    continuous_id.smul (S.continuous_realOrbit u)
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t : ℝ ↦ t • S.realOrbit u t)
      (S.realOrbit u t - t • S.realOrbit x t) t := by
    have hh := (hasDerivAt_id t).smul (hu.hasDerivAt ht)
    simpa only [realOrbit, map_neg, one_smul, smul_neg, sub_eq_add_neg, add_comm] using! hh
  have hi := (S.integrableOn_realOrbit_of_exp_bound hω hbound u).sub
    (S.integrableOn_time_smul_realOrbit hω hbound x)
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt hd hi
    (S.tendsto_time_smul_realOrbit_zero hω hbound u)
  rw [integral_sub (S.integrableOn_realOrbit_of_exp_bound hω hbound u)
    (S.integrableOn_time_smul_realOrbit hω hbound x)] at heq
  simp only [zero_smul, sub_zero] at heq
  exact sub_eq_zero.mp heq

/-- The square of the Laplace resolvent is the transform of the first time
moment, for every vector in the ambient Banach space. -/
theorem laplaceResolvent_sq_apply (S : C0Semigroup ℂ E) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < z.re) (x : E) :
    (S.laplaceResolvent hbound z hz).comp (S.laplaceResolvent hbound z hz) x =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * z) • (t • S.realOrbit x t) := by
  rw [laplaceResolvent, integralRealOrbitCLM_sq_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [realOrbit, rescaleExp_apply, Real.coe_toNNReal _ ht.le, mul_neg, neg_mul]
  exact smul_comm t _ _

end

end C0Semigroup
