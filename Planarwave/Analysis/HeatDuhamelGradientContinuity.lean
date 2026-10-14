/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamelSmoothing

@[expose] public section

/-!
# Time continuity of the smoothed Duhamel derivative

Reverse the integration variable so the heat-gradient singularity is fixed
at zero. Dominated convergence for a parametric primitive then gives BUC
norm continuity, including at the initial time. A continuous extension of
the forcing from a finite interval keeps all hypotheses local in time.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance heatDuhamelContinuityDerivativeNorm : NormedAddCommGroup (E →L[ℝ] F) :=
  inferInstance
local instance heatDuhamelContinuityDerivativeSpace : NormedSpace ℝ (E →L[ℝ] F) :=
  inferInstance

theorem aestronglyMeasurable_heatGradient {a : ℝ} (ha : 0 < a)
    {f : ℝ → BUC E F} (hf : Continuous f) :
    AEStronglyMeasurable (fun s ↦ heatGradient ha s (f s)) volume := by
  have hc : ContinuousOn (fun s ↦ heatGradient ha s (f s)) (Ioi 0) :=
    (continuousOn_heatGradient_joint ha).comp
      (continuous_id.prodMk hf).continuousOn (fun s hs ↦ ⟨hs, mem_univ _⟩)
  have hm := (aestronglyMeasurable_indicator_iff (μ := volume) measurableSet_Ioi).mpr
    (hc.aestronglyMeasurable measurableSet_Ioi)
  convert! hm using 1
  funext s
  by_cases hs : 0 < s
  · simp [hs]
  · simp [hs, heatGradient]

/-- The reversed-time representation fixes the singular heat age at zero. -/
theorem heatDuhamelGradient_eq_reversed {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (f : ℝ → BUC E F) :
    heatDuhamelGradient ha f t = ∫ s in (0 : ℝ)..t, heatGradient ha s (f (t - s)) := by
  rw [heatDuhamelGradient, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht]
  simpa only [sub_sub_cancel, sub_self, sub_zero] using
    intervalIntegral.integral_comp_sub_left
      (fun s ↦ heatGradient ha s (f (t - s))) t (a := 0) (b := t)

theorem heatDuhamelGradient_congr {a t : ℝ} (ha : 0 < a)
    {f g : ℝ → BUC E F} (h : EqOn f g (Icc 0 t)) :
    heatDuhamelGradient ha f t = heatDuhamelGradient ha g t := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [h ⟨hr.1.le, hr.2.le⟩]

/-- The reversed derivative primitive is continuous for globally bounded
continuous forcing, including when the integration endpoint passes zero. -/
theorem continuous_heatGradient_primitive {a C : ℝ} (ha : 0 < a) (_hC : 0 ≤ C)
    {f : ℝ → BUC E F} (hf : Continuous f) (hb : ∀ r, ‖f r‖ ≤ C) :
    Continuous (fun t ↦ ∫ s in (0 : ℝ)..t, heatGradient ha s (f (t - s))) := by
  let w : ℝ → ℝ := (Ioi 0).indicator
    (fun s ↦ (C / Real.sqrt (2 * a)) * s ^ (-(1 / 2 : ℝ)))
  have hi (l r : ℝ) : IntervalIntegrable w volume l r := by
    have hr := (intervalIntegral.intervalIntegrable_rpow' (a := l) (b := r)
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul (C / Real.sqrt (2 * a))
    exact ⟨hr.1.indicator measurableSet_Ioi, hr.2.indicator measurableSet_Ioi⟩
  have hbound (t s : ℝ) : ‖heatGradient ha s (f (t - s))‖ ≤ w s := by
    by_cases hs : 0 < s
    · dsimp only [w]
      rw [indicator_of_mem (show s ∈ Ioi 0 from hs)]
      calc
        _ ≤ C / heatScale a s := (norm_heatGradient_le ha hs _).trans
          (div_le_div_of_nonneg_right (hb _) (heatScale_pos_of_pos ha hs).le)
        _ = _ := by rw [div_eq_mul_inv, inv_heatScale_eq_rpow ha.le hs.le]; ring
    · simp [w, hs, heatGradient]
  apply continuous_iff_continuousAt.mpr
  intro t
  have hp := intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (F := fun t s ↦ heatGradient ha s (f (t - s))) (μ := volume)
    w (min 0 t - 1) (max 0 t + 1) (a₀ := 0) (x₀ := t) (b₀ := t)
    (fun r ↦ (aestronglyMeasurable_heatGradient ha
      (hf.comp (continuous_const.sub continuous_id))).restrict)
    (Filter.Eventually.of_forall fun r ↦ ae_of_all _ (hbound r)) (hi _ _)
    (ae_of_all _ fun s ↦ ((heatGradient ha s).continuous.comp
      (hf.comp (continuous_id.sub continuous_const))).continuousAt)
    (by constructor <;> linarith [le_max_left (0 : ℝ) t, min_le_left (0 : ℝ) t])
    (by constructor <;> linarith [le_max_right (0 : ℝ) t, min_le_right (0 : ℝ) t])
    (measure_singleton t)
  exact hp.comp (f := fun s : ℝ ↦ (s, s)) (continuous_id.prodMk continuous_id).continuousAt

/-- Norm continuity of the actual spatial derivative on a finite horizon. -/
theorem continuousOn_heatDuhamelGradient {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    {f : ℝ → BUC E F} (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (heatDuhamelGradient ha f) (Icc 0 T) := by
  obtain ⟨C, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hb 0 ⟨le_rfl, hT⟩)
  let f₀ := fun r : ℝ ↦ f (projIcc 0 T hT r)
  have hc : Continuous f₀ :=
    (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc
  have hc' := continuous_heatGradient_primitive ha hC hc
    (fun r ↦ hb _ (projIcc 0 T hT r).property)
  apply hc'.continuousOn.congr
  intro t ht
  dsimp only
  rw [← heatDuhamelGradient_eq_reversed ha ht.1 f₀]
  apply heatDuhamelGradient_congr
  intro r hr
  dsimp only [f₀]
  rw [projIcc_of_mem hT ⟨hr.1, hr.2.trans ht.2⟩]

end

end Planarwave
