/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGeneratorDensity
public import Planarwave.Analysis.SemigroupRescale
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The Laplace resolvent of a strongly continuous semigroup

Integration of an exponentially decaying orbit inverts the negative generator. The closed
generator graph justifies passing from finite orbit integrals to the improper integral.
Complex exponential rescaling then gives the resolvent for `Re z > ω`, with the bound
`M / (Re z - ω)`. These are right-half-plane estimates, not yet sectorial estimates.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The operator-norm growth estimate bounds every orbit on nonnegative real time. -/
theorem norm_realOrbit_le_of_exp_bound (S : C0Semigroup ℂ E) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t))
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖S.realOrbit x t‖ ≤ (M * ‖x‖) * Real.exp (ω * t) := by
  have hb := hbound t.toNNReal
  rw [Real.coe_toNNReal _ ht] at hb
  calc
    ‖S.realOrbit x t‖ ≤ ‖S t.toNNReal‖ * ‖x‖ := (S t.toNNReal).le_opNorm x
    _ ≤ (M * Real.exp (ω * t)) * ‖x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg x)
    _ = _ := by ring

/-- Exponentially decaying orbits are Bochner integrable on the positive half-line. -/
theorem integrableOn_realOrbit_of_exp_bound (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    IntegrableOn (S.realOrbit x) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi hω 0).const_mul (M * ‖x‖)).mono'
    (S.continuous_realOrbit x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact S.norm_realOrbit_le_of_exp_bound hbound x ht.le

/-- Exponentially decaying orbits converge to zero at positive infinity. -/
theorem tendsto_realOrbit_zero_of_exp_bound (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    Tendsto (S.realOrbit x) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ ↦ (M * ‖x‖) * Real.exp (ω * t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop hω tendsto_id)).const_mul (M * ‖x‖)
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact S.norm_realOrbit_le_of_exp_bound hbound x ht

/-- The quantitative bound for the integral of an exponentially decaying orbit. -/
theorem norm_integral_realOrbit_le (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    ‖∫ t in Ioi (0 : ℝ), S.realOrbit x t‖ ≤ (M / (-ω)) * ‖x‖ := by
  have hi := (integrableOn_exp_mul_Ioi hω 0).const_mul (M * ‖x‖)
  calc
    ‖∫ t in Ioi (0 : ℝ), S.realOrbit x t‖ ≤
        ∫ t in Ioi (0 : ℝ), (M * ‖x‖) * Real.exp (ω * t) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact S.norm_realOrbit_le_of_exp_bound hbound x ht.le
    _ = (M / (-ω)) * ‖x‖ := by
      rw [integral_const_mul, integral_exp_mul_Ioi hω]
      simp only [mul_zero, Real.exp_zero]
      ring

/-- The improper orbit integral belongs to the full generator domain. -/
theorem hasGeneratorAt_integral_realOrbit (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    S.HasGeneratorAt (∫ t in Ioi (0 : ℝ), S.realOrbit x t) (-x) := by
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (S.integrableOn_realOrbit_of_exp_bound hω hbound x) tendsto_id
  have hz := S.tendsto_realOrbit_zero_of_exp_bound hω hbound x
  have hp : Tendsto
      (fun t : ℝ ↦ (∫ r in 0..t, S.realOrbit x r, S.realOrbit x t - x))
      atTop (𝓝 (∫ r in Ioi (0 : ℝ), S.realOrbit x r, -x)) := by
    simpa only [nhds_prod_eq, zero_sub, id_eq] using! hi.prodMk (hz.sub_const x)
  apply S.isClosed_generatorGraph.mem_of_tendsto hp
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact S.hasGeneratorAt_orbitIntegral x ht

/-- Integrating a generator-domain orbit derivative gives the inverse identity. -/
theorem HasGeneratorAt.integral_realOrbit_eq_neg {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) :
    (∫ t in Ioi (0 : ℝ), S.realOrbit y t) = -x := by
  simpa only [realOrbit_zero, zero_sub] using
    integral_Ioi_of_hasDerivAt_of_tendsto (S.continuous_realOrbit x).continuousWithinAt
      (fun t ht ↦ h.hasDerivAt ht) (S.integrableOn_realOrbit_of_exp_bound hω hbound y)
      (S.tendsto_realOrbit_zero_of_exp_bound hω hbound x)

/-- The improper orbit integral as a bounded linear operator. -/
def integralRealOrbitCLM (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ∫ t in Ioi (0 : ℝ), S.realOrbit x t
      map_add' := by
        intro x y
        simp only [realOrbit, _root_.map_add]
        exact integral_add (S.integrableOn_realOrbit_of_exp_bound hω hbound x)
          (S.integrableOn_realOrbit_of_exp_bound hω hbound y)
      map_smul' := by
        intro a x
        simp only [realOrbit, map_smul, RingHom.id_apply, integral_smul] }
    (M / (-ω)) (S.norm_integral_realOrbit_le hω hbound)

@[simp]
theorem integralRealOrbitCLM_apply (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    S.integralRealOrbitCLM hω hbound x = ∫ t in Ioi (0 : ℝ), S.realOrbit x t := rfl

/-- Complex rescaling gives an exponentially decaying bound in the resolvent half-plane. -/
theorem norm_rescaleExp_neg_le (S : C0Semigroup ℂ E) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (t : NNReal) :
    ‖S.rescaleExp (-z) t‖ ≤ M * Real.exp ((ω - z.re) * t) := by
  rw [norm_rescaleExp]
  calc
    Real.exp ((t : ℝ) * (-z).re) * ‖S t‖ ≤
        Real.exp ((t : ℝ) * (-z).re) * (M * Real.exp (ω * t)) := by
      gcongr
      exact hbound t
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      simp only [Complex.neg_re]
      ring

/-- The Laplace resolvent `(z I - A)⁻¹` in the right half-plane of a growth bound. -/
def laplaceResolvent (S : C0Semigroup ℂ E) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) :
    E →L[ℂ] E :=
  (S.rescaleExp (-z)).integralRealOrbitCLM (sub_neg.mpr hz) (S.norm_rescaleExp_neg_le hbound z)

/-- The usual Laplace-transform formula, with the weight written explicitly. -/
theorem laplaceResolvent_apply (S : C0Semigroup ℂ E) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) (x : E) :
    S.laplaceResolvent hbound z hz x =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * z) • S.realOrbit x t := by
  change (∫ t in Ioi (0 : ℝ), (S.rescaleExp (-z)).realOrbit x t) = _
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [realOrbit, rescaleExp_apply, Real.coe_toNNReal _ ht.le, mul_neg, neg_mul]

/-- Resolvent norm bound in terms of the semigroup growth estimate. -/
theorem norm_laplaceResolvent_le (S : C0Semigroup ℂ E) {M ω : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) :
    ‖S.laplaceResolvent hbound z hz‖ ≤ M / (z.re - ω) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  simpa only [neg_sub, laplaceResolvent, integralRealOrbitCLM_apply] using!
    (S.rescaleExp (-z)).norm_integral_realOrbit_le (sub_neg.mpr hz)
      (S.norm_rescaleExp_neg_le hbound z) x

/-- Right inverse of `z I - A`, including membership in the full generator domain. -/
theorem hasGeneratorAt_laplaceResolvent (S : C0Semigroup ℂ E) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) (x : E) :
    S.HasGeneratorAt (S.laplaceResolvent hbound z hz x) (z • S.laplaceResolvent hbound z hz x - x) := by
  have h : (S.rescaleExp (-z)).HasGeneratorAt (S.laplaceResolvent hbound z hz x) (-x) :=
    (S.rescaleExp (-z)).hasGeneratorAt_integral_realOrbit (sub_neg.mpr hz)
      (S.norm_rescaleExp_neg_le hbound z) x
  rw [rescaleExp_hasGeneratorAt_iff] at h
  have heq : -x - (-z) • S.laplaceResolvent hbound z hz x =
      z • S.laplaceResolvent hbound z hz x - x := by rw [neg_smul]; abel
  rwa [heq] at h

/-- Left inverse of `z I - A` on its generator domain. -/
theorem HasGeneratorAt.laplaceResolvent_apply {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (hz : ω < z.re) :
    S.laplaceResolvent hbound z hz (z • x - y) = x := by
  have hi := (h.rescaleExp (-z)).integral_realOrbit_eq_neg (sub_neg.mpr hz)
    (S.norm_rescaleExp_neg_le hbound z)
  change S.laplaceResolvent hbound z hz (y + (-z) • x) = -x at hi
  have heq : y + (-z) • x = -(z • x - y) := by rw [neg_smul]; abel
  rw [heq, map_neg, neg_inj] at hi
  exact hi

end

end C0Semigroup
