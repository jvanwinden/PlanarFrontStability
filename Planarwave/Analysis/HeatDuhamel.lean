/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingSmoothing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Continuous heat Duhamel trajectories

These facts support both the tracking cancellation and the construction of
the forced Cole--Hopf mild solution. All integrals are BUC-valued; continuity
of the heat operators in operator norm at time zero is not assumed.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The transverse heat Duhamel integral in real BUC space. -/
def heatDuhamel (a : ℝ) (g : ℝ → BUC E F) (t : ℝ) : BUC E F :=
  ∫ r in (0 : ℝ)..t, heatFlowBUC a (t - r) (g r)

@[simp]
theorem heatDuhamel_zero (a : ℝ) (g : ℝ → BUC E F) : heatDuhamel a g 0 = 0 := by
  simp [heatDuhamel]

theorem continuous_heatDuhamel_integrand (a : ℝ) {g : ℝ → BUC E F} (hg : Continuous g) :
    Continuous (fun p : ℝ × ℝ ↦ heatFlowBUC a (p.1 - p.2) (g p.2)) :=
  (continuous_heatFlowBUC_joint a).comp
    ((continuous_fst.sub continuous_snd).prodMk (hg.comp continuous_snd))

/-- Continuous forcing gives norm continuity of the Duhamel trajectory,
including the initial time. -/
theorem continuous_heatDuhamel (a : ℝ) {g : ℝ → BUC E F} (hg : Continuous g) :
    Continuous (heatDuhamel a g) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (continuous_heatDuhamel_integrand a hg) continuous_id

theorem heatDuhamel_add (a : ℝ) {f g : ℝ → BUC E F}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    heatDuhamel a (fun r ↦ f r + g r) t = heatDuhamel a f t + heatDuhamel a g t := by
  simp only [heatDuhamel, heatFlowBUC_add]
  apply intervalIntegral.integral_add
  · exact ((continuous_heatDuhamel_integrand a hf).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  · exact ((continuous_heatDuhamel_integrand a hg).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t

theorem heatDuhamel_smul (a c : ℝ) (g : ℝ → BUC E F) (t : ℝ) :
    heatDuhamel a (fun r ↦ c • g r) t = c • heatDuhamel a g t := by
  simp only [heatDuhamel, heatFlowBUC_smul, intervalIntegral.integral_smul]

/-- Only the source values between zero and the current time enter Duhamel. -/
theorem heatDuhamel_congr (a : ℝ) {f g : ℝ → BUC E F} {t : ℝ} (ht : 0 ≤ t)
    (h : EqOn f g (Icc 0 t)) : heatDuhamel a f t = heatDuhamel a g t := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht] at hr
  dsimp only
  rw [h hr]

/-- Contractivity supplies the small time factor in the Volterra bound. -/
theorem norm_heatDuhamel_le {a t C : ℝ} (g : ℝ → BUC E F) (ht : 0 ≤ t)
    (hg : ∀ r ∈ Icc 0 t, ‖g r‖ ≤ C) : ‖heatDuhamel a g t‖ ≤ C * t := by
  have h : ∀ r ∈ uIoc (0 : ℝ) t, ‖heatFlowBUC a (t - r) (g r)‖ ≤ C := by
    intro r hr
    rw [uIoc_of_le ht] at hr
    exact (norm_heatFlowBUC_le _ _ _).trans (hg r ⟨hr.1.le, hr.2⟩)
  simpa only [heatDuhamel, sub_zero, abs_of_nonneg ht] using!
    intervalIntegral.norm_integral_le_of_norm_le_const h

/-- Split Duhamel at an intermediate time: the old history propagates by
heat, and only the source after that time must be integrated again. -/
theorem heatDuhamel_restart {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s ≤ t)
    (g : ℝ → BUC E F) (hg : ContinuousOn g (Icc 0 t)) :
    heatDuhamel a g t = heatFlowBUC a (t - s) (heatDuhamel a g s) +
      ∫ r in s..t, heatFlowBUC a (t - r) (g r) := by
  have hc : ContinuousOn (fun r ↦ heatFlowBUC a (t - r) (g r)) (Icc 0 t) :=
    (continuous_heatFlowBUC_joint a).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hg)
  have hi₁ := (hc.mono (Icc_subset_Icc le_rfl hst)).intervalIntegrable_of_Icc (μ := volume) hs
  have hi₂ := (hc.mono (Icc_subset_Icc hs le_rfl)).intervalIntegrable_of_Icc (μ := volume) hst
  have his : IntervalIntegrable (fun r ↦ heatFlowBUC a (s - r) (g r)) volume 0 s :=
    ((continuous_heatFlowBUC_joint a).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk
        (hg.mono (Icc_subset_Icc le_rfl hst)))).intervalIntegrable_of_Icc hs
  have htransport : heatFlowBUC a (t - s) (heatDuhamel a g s) =
      ∫ r in (0 : ℝ)..s, heatFlowBUC a (t - r) (g r) := by
    change (heatOperator a (t - s)) (∫ r in (0 : ℝ)..s, heatFlowBUC a (s - r) (g r)) = _
    rw [← (heatOperator a (t - s)).intervalIntegral_comp_comm his]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs] at hr
    change heatFlowBUC a (t - s) (heatFlowBUC a (s - r) (g r)) = _
    rw [← heatFlowBUC_add_apply ha (sub_nonneg.mpr hst) (sub_nonneg.mpr hr.2)]
    congr 1
    ring
  rw [htransport]
  exact (intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂).symm

end

end Planarwave
