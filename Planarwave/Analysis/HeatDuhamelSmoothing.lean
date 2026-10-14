/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatGradientOperator
public import Planarwave.Analysis.BUCSpatialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# One-derivative smoothing of heat Duhamel integrals

Continuous BUC forcing gains one genuine spatial BUC derivative, without
any derivative assumption on the forcing. The heat-gradient singularity
at the upper integration endpoint is integrable and gives a square-root
time bound. This is the first regularity gain in the parabolic bootstrap
used in Step 4 of the paper.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Planarwave

noncomputable section

theorem inv_heatScale_eq_rpow {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    (heatScale a s)⁻¹ = (Real.sqrt (2 * a))⁻¹ * s ^ (-(1 / 2 : ℝ)) := by
  rw [heatScale, Real.sqrt_mul (mul_nonneg (by norm_num) ha), mul_inv_rev,
    Real.rpow_neg hs, Real.sqrt_eq_rpow]
  ring

theorem intervalIntegrable_heatGradientWeight (t : ℝ) :
    IntervalIntegrable (fun r ↦ (t - r) ^ (-(1 / 2 : ℝ))) volume 0 t := by
  simpa only [sub_zero, sub_self] using
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_left t).symm

theorem integral_heatGradientWeight (t : ℝ) :
    (∫ r in (0 : ℝ)..t, (t - r) ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt t := by
  rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ s ^ (-(1 / 2 : ℝ))) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num
  rw [Real.sqrt_eq_rpow]
  ring

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance heatDuhamelSmoothingDerivativeNorm : NormedAddCommGroup (E →L[ℝ] F) :=
  inferInstance
local instance heatDuhamelSmoothingDerivativeSpace : NormedSpace ℝ (E →L[ℝ] F) :=
  inferInstance

/-- The spatial derivative integrand is continuous before the terminal time. -/
theorem continuousOn_heatGradient_integrand {a t : ℝ} (ha : 0 < a)
    {f : ℝ → BUC E F} (hf : ContinuousOn f (Icc 0 t)) :
    ContinuousOn (fun r ↦ heatGradient ha (t - r) (f r)) (Ioo 0 t) := by
  apply (continuousOn_heatGradient_joint ha).comp
    ((continuousOn_const.sub continuousOn_id).prodMk (hf.mono Ioo_subset_Icc_self))
  intro r hr
  exact ⟨sub_pos.mpr hr.2, mem_univ _⟩

theorem norm_heatGradient_integrand_le {a t C : ℝ} (ha : 0 < a)
    {f : ℝ → BUC E F} (hb : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ C)
    {r : ℝ} (hr : r ∈ Ioo 0 t) :
    ‖heatGradient ha (t - r) (f r)‖ ≤
      (C / Real.sqrt (2 * a)) * (t - r) ^ (-(1 / 2 : ℝ)) := by
  calc
    _ ≤ C / heatScale a (t - r) :=
      (norm_heatGradient_le ha (sub_pos.mpr hr.2) (f r)).trans
        (div_le_div_of_nonneg_right (hb r ⟨hr.1.le, hr.2.le⟩)
          (heatScale_pos_of_pos ha (sub_pos.mpr hr.2)).le)
    _ = _ := by
      rw [div_eq_mul_inv, inv_heatScale_eq_rpow ha.le (sub_nonneg.mpr hr.2.le)]
      ring

/-- Integrability includes the singular terminal endpoint. -/
theorem integrableOn_heatGradient_integrand {a t C : ℝ} (ha : 0 < a) (_ht : 0 ≤ t)
    {f : ℝ → BUC E F} (hf : ContinuousOn f (Icc 0 t))
    (hb : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ C) :
    IntegrableOn (fun r ↦ heatGradient ha (t - r) (f r)) (Ioo 0 t) := by
  have hi := ((intervalIntegrable_heatGradientWeight t).const_mul
    (C / Real.sqrt (2 * a))).1.mono_set Ioo_subset_Ioc_self
  apply hi.mono' ((continuousOn_heatGradient_integrand ha hf).aestronglyMeasurable
    measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact norm_heatGradient_integrand_le ha hb hr

/-- The BUC-valued gradient of the Duhamel response. -/
def heatDuhamelGradient {a : ℝ} (ha : 0 < a) (f : ℝ → BUC E F) (t : ℝ) :
    BUC E (E →L[ℝ] F) :=
  ∫ r in Ioo 0 t, heatGradient ha (t - r) (f r)

theorem norm_heatDuhamelGradient_le {a t C : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    {f : ℝ → BUC E F} (hb : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ C) :
    ‖heatDuhamelGradient ha f t‖ ≤ (C / Real.sqrt (2 * a)) * (2 * Real.sqrt t) := by
  have hi := ((intervalIntegrable_heatGradientWeight t).const_mul
    (C / Real.sqrt (2 * a))).1.mono_set Ioo_subset_Ioc_self
  calc
    _ ≤ ∫ r in Ioo 0 t, (C / Real.sqrt (2 * a)) * (t - r) ^ (-(1 / 2 : ℝ)) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact norm_heatGradient_integrand_le ha hb hr
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht,
        intervalIntegral.integral_const_mul, integral_heatGradientWeight]

/-- The integrated heat gradient is the actual spatial derivative, even
when the forcing itself has no spatial derivative. -/
theorem hasFDerivAt_heatDuhamel_smoothing {a t C : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    {f : ℝ → BUC E F} (hf : ContinuousOn f (Icc 0 t))
    (hb : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ C) (x : E) :
    HasFDerivAt (heatDuhamel a f t) (heatDuhamelGradient ha f t x) x := by
  have hv : IntegrableOn (fun r ↦ heatFlowBUC a (t - r) (f r)) (Ioo 0 t) :=
    (((continuous_heatFlowBUC_joint a).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hf)).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self
  have hd := integrableOn_heatGradient_integrand ha ht hf hb
  have hval : (heatDuhamel a f t : E → F) =
      fun y ↦ ∫ r in Ioo 0 t, heatFlowBUC a (t - r) (f r) y := by
    funext y
    rw [heatDuhamel, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
    exact ((BUC.evalCLM (𝕜 := ℝ) y).integral_comp_comm hv).symm
  rw [hval]
  change HasFDerivAt _ ((BUC.evalCLM (𝕜 := ℝ) x)
    (∫ r in Ioo 0 t, heatGradient ha (t - r) (f r))) x
  rw [← (BUC.evalCLM (𝕜 := ℝ) x).integral_comp_comm hd]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y r ↦ heatGradient ha (t - r) (f r) y)
    (bound := fun r ↦ (C / Real.sqrt (2 * a)) * (t - r) ^ (-(1 / 2 : ℝ)))
    (s := univ) Filter.univ_mem
  · exact Filter.Eventually.of_forall fun y ↦
      ((BUC.evalCLM (𝕜 := ℝ) y).integrable_comp hv).aestronglyMeasurable
  · exact (BUC.evalCLM (𝕜 := ℝ) x).integrable_comp hv
  · exact ((BUC.evalCLM (𝕜 := ℝ) x).integrable_comp hd).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro y _
    exact ((heatGradient ha (t - r) (f r)).norm_apply_le y).trans
      (norm_heatGradient_integrand_le ha hb hr)
  · exact ((intervalIntegrable_heatGradientWeight t).const_mul
      (C / Real.sqrt (2 * a))).1.mono_set Ioo_subset_Ioc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    intro y _
    exact hasFDerivAt_heatFlow_gradient ha (sub_pos.mpr hr.2) (f r) y

end

end Planarwave
