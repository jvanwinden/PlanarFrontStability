/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupLaplaceMoment
public import Planarwave.Analysis.ResolventContour
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-! # Differentiated Laplace inversion for semigroups

Fourier inversion of the damped first time moment gives an absolutely
convergent vertical integral. The time factor avoids the nonintegrable
inverse-linear tail of the unsquared resolvent.
-/

open Filter MeasureTheory Set Topology
open scoped FourierTransform

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Extend the damped first time moment by zero to negative time. -/
def dampedTimeOrbit (S : C0Semigroup ℂ E) (γ : ℝ) (x : E) : ℝ → E :=
  (Ioi 0).indicator (fun t : ℝ ↦ Complex.exp (-(t : ℂ) * γ) • (t • S.realOrbit x t))

theorem integrable_dampedTimeOrbit (S : C0Semigroup ℂ E) {M ω γ : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (hγ : ω < γ) (x : E) :
    Integrable (S.dampedTimeOrbit γ x) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  have hi := (S.rescaleExp (-(γ : ℂ))).integrableOn_time_smul_realOrbit
    (by simpa using sub_neg.mpr hγ) (S.norm_rescaleExp_neg_le hbound (γ : ℂ)) x
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [realOrbit, rescaleExp_apply, Real.coe_toNNReal _ ht.le, mul_neg, neg_mul]
  exact smul_comm t _ _

theorem continuousAt_dampedTimeOrbit (S : C0Semigroup ℂ E) (γ : ℝ) (x : E)
    {t : ℝ} (ht : 0 < t) : ContinuousAt (S.dampedTimeOrbit γ x) t := by
  have he : Continuous (fun t : ℝ ↦ Complex.exp (-(t : ℂ) * γ)) := by fun_prop
  have hc : Continuous (fun t : ℝ ↦ Complex.exp (-(t : ℂ) * γ) • (t • S.realOrbit x t)) :=
    he.smul (continuous_id.smul (S.continuous_realOrbit x))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  exact indicator_of_mem hr _

/-- Fourier transform of the damped first time moment is the squared Laplace
resolvent, with the Fourier library's `2π` normalization. -/
theorem fourier_dampedTimeOrbit (S : C0Semigroup ℂ E) {M ω γ : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (hγ : ω < γ) (x : E) (s : ℝ) :
    𝓕 (S.dampedTimeOrbit γ x) s =
      (S.laplaceResolvent hbound (γ + (2 * Real.pi * s : ℝ) * Complex.I) (by simpa using hγ)).comp
        (S.laplaceResolvent hbound (γ + (2 * Real.pi * s : ℝ) * Complex.I) (by simpa using hγ)) x := by
  rw [S.laplaceResolvent_sq_apply, Real.fourier_eq']
  simp only [dampedTimeOrbit]
  simp_rw [← indicator_smul_apply (Ioi 0)
    (fun t : ℝ ↦ Complex.exp ((-2 * Real.pi * inner ℝ t s : ℝ) * Complex.I))
    (fun t : ℝ ↦ Complex.exp (-(t : ℂ) * γ) • (t • S.realOrbit x t))]
  rw [integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

end

end C0Semigroup

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

/-- Differentiated Laplace inversion on vectors. Fourier inversion applies
because the time moment and its squared-resolvent transform are both integrable. -/
theorem time_smul_orbit_eq_squaredResolvent_integral (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {M ω γ C : ℝ} (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (hγ : ω < γ)
    (hRbound : ∀ y : ℝ, ‖A.ambientResolvent (γ + y * Complex.I)‖ ≤ C / (1 + |y|))
    {t : ℝ} (ht : 0 < t) (x : E) :
    t • S.realOrbit x t = (2 * Real.pi)⁻¹ •
      ∫ y : ℝ, A.squaredResolventKernel t (γ + y * Complex.I) x := by
  let f := S.dampedTimeOrbit γ x
  have hres (y : ℝ) : A.IsInResolvent (γ + y * Complex.I) :=
    A.isInResolvent_of_semigroup_bound S hgen hbound _ (by simpa using hγ)
  have hfourier (s : ℝ) : 𝓕 f s =
      (A.ambientResolvent (γ + (2 * Real.pi * s : ℝ) * Complex.I)).comp
        (A.ambientResolvent (γ + (2 * Real.pi * s : ℝ) * Complex.I)) x := by
    rw [A.ambientResolvent_eq_neg_laplace S hgen hbound _ (by simpa using hγ)]
    simpa only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, neg_neg] using
      S.fourier_dampedTimeOrbit hbound hγ x s
  have hF : Integrable (𝓕 f) := by
    have hi := (ContinuousLinearMap.apply ℂ E x).integrable_comp
      (A.integrable_ambientResolvent_sq hres hRbound)
    apply (hi.comp_mul_left' (R := 2 * Real.pi) (by positivity)).congr
    filter_upwards [] with s
    exact (hfourier s).symm
  have hinv := (S.integrable_dampedTimeOrbit hbound hγ x).fourierInv_fourier_eq hF
    (S.continuousAt_dampedTimeOrbit γ x ht)
  have hweighted : Complex.exp ((t : ℂ) * γ) • 𝓕⁻ (𝓕 f) t = t • S.realOrbit x t := by
    rw [hinv]
    rw [C0Semigroup.dampedTimeOrbit, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    simp only [smul_smul,
      ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_smul]
  have hkernel : Complex.exp ((t : ℂ) * γ) • 𝓕⁻ (𝓕 f) t =
      ∫ s : ℝ, A.squaredResolventKernel t (γ + (2 * Real.pi * s : ℝ) * Complex.I) x := by
    rw [Real.fourierInv_eq', ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with s
    rw [hfourier]
    simp only [squaredResolventKernel, smul_apply, smul_smul,
      ← Complex.exp_add]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  rw [← hweighted, hkernel]
  simpa only [abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)] using
    Measure.integral_comp_mul_left
      (fun y : ℝ ↦ A.squaredResolventKernel t (γ + y * Complex.I) x) (2 * Real.pi)

/-- Operator-valued differentiated Laplace inversion, with the normalization
needed for the subsequent contour shift. -/
theorem time_smul_semigroup_eq_squaredResolvent_integral (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {M ω γ C : ℝ} (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (hγ : ω < γ)
    (hRbound : ∀ y : ℝ, ‖A.ambientResolvent (γ + y * Complex.I)‖ ≤ C / (1 + |y|))
    {t : ℝ} (ht : 0 < t) :
    t • S t.toNNReal = (2 * Real.pi)⁻¹ •
      ∫ y : ℝ, A.squaredResolventKernel t (γ + y * Complex.I) := by
  have hres : ∀ z : ℂ, γ ≤ z.re → z.re ≤ γ → A.IsInResolvent z := by
    intro z hz _
    exact A.isInResolvent_of_semigroup_bound S hgen hbound z (hγ.trans_le hz)
  have hb : ∀ z : ℂ, γ ≤ z.re → z.re ≤ γ → ‖A.ambientResolvent z‖ ≤ C / (1 + |z.im|) := by
    intro z h₁ h₂
    have hzre : z.re = γ := le_antisymm h₂ h₁
    have hh := hRbound z.im
    rw [← hzre, Complex.re_add_im] at hh
    exact hh
  have hi := integrable_vertical_of_quadratic_bound
    (fun z h₁ h₂ ↦ A.differentiableAt_squaredResolventKernel t (hres z h₁ h₂))
    (fun z h₁ h₂ ↦ A.norm_squaredResolventKernel_le hb ht.le (z := z) h₁ h₂)
    (r := γ) ⟨le_rfl, le_rfl⟩
  apply ContinuousLinearMap.ext
  intro x
  simpa only [smul_apply, ContinuousLinearMap.integral_apply hi,
    C0Semigroup.realOrbit] using
    A.time_smul_orbit_eq_squaredResolvent_integral S hgen hbound hγ hRbound ht x

end

end Planarwave.ClosedOperator
