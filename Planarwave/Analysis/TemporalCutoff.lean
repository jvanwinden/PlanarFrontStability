/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCCompactSupport
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The temporal cutoff in the tracking scheme

Construct the smooth nonnegative unit-mass cutoff supported on `[1/4,3/4]`
specified in Section 1.3 and used in the delayed forcing in Section 4.2.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Planarwave

noncomputable section

def trackingBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The paper's temporal cutoff `ρ`, normalized with respect to Lebesgue measure. -/
def trackingCutoff : BUC ℝ ℝ :=
  BUC.ofCompactSupport (trackingBump.normed volume)
    trackingBump.continuous_normed trackingBump.hasCompactSupport_normed

theorem contDiff_trackingCutoff : ContDiff ℝ ∞ (trackingCutoff : ℝ → ℝ) :=
  trackingBump.contDiff_normed

theorem trackingCutoff_nonneg (t : ℝ) : 0 ≤ trackingCutoff t :=
  trackingBump.nonneg_normed t

theorem integrable_trackingCutoff : Integrable (trackingCutoff : ℝ → ℝ) :=
  trackingBump.integrable_normed

theorem integral_trackingCutoff : (∫ t, trackingCutoff t) = 1 :=
  trackingBump.integral_normed

/-- The cutoff actually vanishes at the two endpoints of its support interval. -/
theorem trackingCutoff_ne_zero_mem {t : ℝ} (ht : trackingCutoff t ≠ 0) :
    t ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
  have h : t ∈ Function.support (trackingBump.normed volume) := ht
  rw [trackingBump.support_normed_eq] at h
  have hdist : |t - 1 / 2| < (1 / 4 : ℝ) := by
    simpa only [Metric.mem_ball, Real.dist_eq, trackingBump] using h
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hdist
  constructor <;> linarith

theorem trackingCutoff_eq_zero_of_not_mem {t : ℝ}
    (ht : t ∉ Ioo (1 / 4 : ℝ) (3 / 4)) : trackingCutoff t = 0 := by
  by_contra h
  exact ht (trackingCutoff_ne_zero_mem h)

theorem trackingCutoff_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : trackingCutoff t = 0 :=
  trackingCutoff_eq_zero_of_not_mem (fun h ↦ (not_lt_of_ge ht) h.1)

theorem trackingCutoff_eq_zero_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) : trackingCutoff t = 0 :=
  trackingCutoff_eq_zero_of_not_mem (fun h ↦ (not_lt_of_ge ht) h.2)

theorem trackingCutoff_le_norm (t : ℝ) : trackingCutoff t ≤ ‖trackingCutoff‖ :=
  (le_abs_self _).trans (trackingCutoff.norm_apply_le t)

/-- Any interval containing the support captures the full unit mass. -/
theorem integral_trackingCutoff_of_bounds {a b : ℝ} (ha : a ≤ 1 / 4) (hb : 3 / 4 ≤ b) :
    (∫ t in a..b, trackingCutoff t) = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset, integral_trackingCutoff]
  intro t ht
  have h := trackingCutoff_ne_zero_mem ht
  exact ⟨ha.trans_lt h.1, h.2.le.trans hb⟩

/-- Every fully completed translated pulse has unit mass in the Duhamel interval. -/
theorem integral_trackingCutoff_shift_completed {b t : ℝ} (hb : 0 ≤ b) (ht : b + 1 ≤ t) :
    (∫ r in (0 : ℝ)..t, trackingCutoff (r - b)) = 1 := by
  rw [intervalIntegral.integral_comp_sub_right]
  exact integral_trackingCutoff_of_bounds (by linarith) (by linarith)

/-- A partially accumulated pulse has mass between zero and one. -/
theorem integral_trackingCutoff_shift_mem {b t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, trackingCutoff (r - b)) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall ht (fun r ↦ trackingCutoff_nonneg (r - b))
  · rw [intervalIntegral.integral_comp_sub_right,
      intervalIntegral.integral_of_le (sub_le_sub_right ht b), ← integral_trackingCutoff]
    exact MeasureTheory.setIntegral_le_integral integrable_trackingCutoff
      (ae_of_all _ trackingCutoff_nonneg)

end

end Planarwave
