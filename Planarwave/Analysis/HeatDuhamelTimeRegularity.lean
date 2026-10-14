/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamel
public import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Time differentiation of the heat variation-of-constants formula

Rescaling the short Duhamel integral gives its derivative at zero. Restarting
then gives a right derivative for spatially twice BUC differentiable mild
solutions. A continuous right derivative determines the integral equation,
and hence the full classical derivative at interior times.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Planarwave

noncomputable section

section Calculus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Continuous right derivatives determine the trajectory, including both
endpoints of a compact interval. -/
theorem eq_initial_add_integral_of_hasDerivWithinAt_right {u v : ℝ → V} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : Continuous v)
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt u (v t) (Ici t) t) :
    ∀ t ∈ Icc a b, u t = (∫ r in a..t, v r) + u a := by
  apply eq_of_has_deriv_right_eq hd
  · intro t _
    exact ((hv.integral_hasStrictDerivAt a t).hasDerivAt.add_const (u a)).hasDerivWithinAt
  · exact hu
  · exact ((intervalIntegral.differentiable_integral_of_continuous hv).continuous.add
      continuous_const).continuousOn
  · simp

/-- A continuous right derivative is the derivative within the whole
closed interval, including the left derivative at the final time. -/
theorem hasDerivWithinAt_of_continuous_right_derivative {u v : ℝ → V} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : Continuous v)
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt u (v t) (Ici t) t)
    {t : ℝ} (ht : t ∈ Icc a b) : HasDerivWithinAt u (v t) (Icc a b) t := by
  apply ((hv.integral_hasStrictDerivAt a t).hasDerivAt.add_const (u a)).hasDerivWithinAt.congr_of_mem
  · intro r hr
    exact eq_initial_add_integral_of_hasDerivWithinAt_right hu hv hd r hr
  · exact ht

end Calculus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The time derivative at zero of Duhamel is the initial source. This
uses strong continuity, not operator-norm continuity of the heat flow. -/
theorem hasDerivAt_heatDuhamel_zero (a : ℝ) {f : ℝ → BUC E F} (hf : Continuous f) :
    HasDerivAt (heatDuhamel a f) (f 0) 0 := by
  let A : ℝ → BUC E F := fun t ↦ ∫ r in (0 : ℝ)..1, heatFlowBUC a (t - t * r) (f (t * r))
  have hAc : Continuous A := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (continuous_heatFlowBUC_joint a).comp
      ((continuous_fst.sub (continuous_fst.mul continuous_snd)).prodMk
        (hf.comp (continuous_fst.mul continuous_snd)))
  have hA0 : A 0 = f 0 := by simp [A]
  have hlim : Tendsto A (𝓝[≠] 0) (𝓝 (f 0)) :=
    hA0 ▸ hAc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hasDerivAt_iff_tendsto_slope]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have heq : A t = t⁻¹ • heatDuhamel a f t := by
    simpa only [mul_zero, mul_one, A, heatDuhamel] using!
      intervalIntegral.integral_comp_mul_left (fun r ↦ heatFlowBUC a (t - r) (f r))
        ht0 (a := 0) (b := 1)
  simpa only [slope, vsub_eq_sub, sub_zero, heatDuhamel_zero] using heq

/-- Change the origin of time in a Duhamel interval. -/
theorem heatDuhamel_shift (a s t : ℝ) (f : ℝ → BUC E F) :
    heatDuhamel a (fun r ↦ f (s + r)) (t - s) =
      ∫ r in s..t, heatFlowBUC a (t - r) (f r) := by
  have heq : (fun r ↦ heatFlowBUC a (t - s - r) (f (s + r))) =
      fun r ↦ heatFlowBUC a (t - (s + r)) (f (s + r)) := by
    funext r
    congr 1
    ring
  rw [heatDuhamel, heq]
  simpa using intervalIntegral.integral_comp_add_left
    (fun r ↦ heatFlowBUC a (t - r) (f r)) s (a := 0) (b := t - s)

/-- A restarted heat solution with two BUC spatial derivatives has the
expected right time derivative at the restart time. -/
theorem hasDerivWithinAt_heat_restart {a s T : ℝ} (ha : 0 < a) (hsT : s < T)
    {u f : ℝ → BUC E F} (hf : Continuous f)
    (q : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hq : ∀ x, HasFDerivAt (u s) (q x) x) (hh : ∀ x, HasFDerivAt q (h x) x)
    (heq : ∀ t ∈ Icc s T, u t = heatFlowBUC a (t - s) (u s) +
      ∫ r in s..t, heatFlowBUC a (t - r) (f r)) :
    HasDerivWithinAt u (convectiveGeneratorBUC a 0 q h + f s) (Ici s) s := by
  have hheat : HasDerivWithinAt (fun r ↦ heatFlowBUC a r (u s))
      (convectiveGeneratorBUC a 0 q h) (Ici 0) 0 := by
    simpa only [convectiveHeatFlowBUC, smul_zero, neg_zero, BUC.translate_zero] using
      hasDerivWithinAt_convectiveHeatFlowBUC_zero_fderiv ha 0 (u s) q h hq hh
  have hduh := hasDerivAt_heatDuhamel_zero a (f := fun z ↦ f (s + z))
    (hf.comp (continuous_const.add continuous_id))
  have hd : HasDerivWithinAt
      (fun r ↦ heatFlowBUC a r (u s) + heatDuhamel a (fun z ↦ f (s + z)) r)
      (convectiveGeneratorBUC a 0 q h + f s) (Ici 0) 0 := by
    simpa only [add_zero, Pi.add_apply] using! hheat.add hduh.hasDerivWithinAt
  have hshift := hd.scomp_of_eq s ((hasDerivWithinAt_id s (Ici s)).sub_const s)
    (fun r hr ↦ show 0 ≤ r - s from sub_nonneg.mpr hr) (sub_self s).symm
  simp only [one_smul] at hshift
  apply hshift.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hsT)] with r hr hrT
    simpa only [Function.comp_def, id_eq, heatDuhamel_shift] using! heq r ⟨hr, hrT.le⟩
  · simpa only [Function.comp_def, id_eq, heatDuhamel_shift] using! heq s ⟨le_rfl, hsT.le⟩

end

end Planarwave
