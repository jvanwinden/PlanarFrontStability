/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.LogarithmicDecayWeights

@[expose] public section

/-!
# Time-integral bounds for the improved forcing

The weight `(1+t)^(-3/2) log(2+t)` in the last proof of the paper has
uniformly bounded time mass. These bounds are independent of the horizon
and apply to the heat Duhamel terms in the Cole--Hopf comparison.
-/

open MeasureTheory Set

namespace Planarwave

theorem logarithmic_decay_le_five_quarters {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) ≤ 8 * (1 + t) ^ (-(5 : ℝ) / 4) := by
  have hlog : Real.log (2 + t) ≤ 8 * (1 + t) ^ (1 / 4 : ℝ) := by
    have hpow : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
    calc
      _ ≤ (2 + t) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := Real.log_le_rpow_div (by linarith) (by norm_num)
      _ ≤ (2 * (1 + t)) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)) (by norm_num)
      _ = (4 * (2 : ℝ) ^ (1 / 4 : ℝ)) * (1 + t) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1 + t)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (1 + t) ^ (-(3 : ℝ) / 2) * (8 * (1 + t) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (by linarith) _)
    _ = _ := by rw [mul_left_comm, ← Real.rpow_add (by linarith : 0 < 1 + t)]; norm_num

/-- A uniform time-mass bound for the paper's improved forcing weight. -/
theorem integral_logarithmic_decay_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r)) ≤ 32 := by
  have hc := continuousOn_logarithmic_decay ((3 : ℝ) / 2) t
  have hp : ContinuousOn (fun r : ℝ ↦ (1 + r) ^ (-(5 : ℝ) / 4)) (Icc 0 t) :=
    (continuousOn_const.add continuousOn_id).rpow_const
      (fun r hr ↦ Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))
  calc
    _ ≤ ∫ r in (0 : ℝ)..t, 8 * (1 + r) ^ (-(5 : ℝ) / 4) :=
      intervalIntegral.integral_mono_on ht
        (by simpa only [neg_div] using hc.intervalIntegrable_of_Icc ht)
        ((hp.const_mul 8).intervalIntegrable_of_Icc ht)
        (fun r hr ↦ logarithmic_decay_le_five_quarters hr.1)
    _ = 8 * ∫ r in (0 : ℝ)..t, (1 + r) ^ (-(5 : ℝ) / 4) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by linarith [integral_one_add_rpow_neg_five_quarters_le ht]

/-- The same bound applies after a nonnegative restart time. -/
theorem integral_logarithmic_decay_subinterval_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r in s..t, (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r)) ≤ 32 := by
  apply le_trans _ (integral_logarithmic_decay_le (hs.trans hst))
  apply intervalIntegral.integral_mono_interval hs hst le_rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (Real.rpow_nonneg (by linarith [hr.1]) _) (Real.log_nonneg (by linarith [hr.1]))
  · simpa only [neg_div] using
      (continuousOn_logarithmic_decay ((3 : ℝ) / 2) t).intervalIntegrable_of_Icc (hs.trans hst)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Heat contractivity converts the improved forcing weight to a
uniform bound on its restarted Duhamel contribution. -/
theorem norm_heat_integral_le_logarithmic_decay (a : ℝ) (g : ℝ → BUC E F)
    {s t A : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hA : 0 ≤ A)
    (hb : ∀ r ∈ Icc s t, ‖g r‖ ≤ A * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r)) :
    ‖∫ r in s..t, heatFlowBUC a (t - r) (g r)‖ ≤ 32 * A := by
  have hc : ContinuousOn (fun r ↦ A * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r)) (Icc s t) := by
    simpa only [neg_div, mul_assoc] using
      ((continuousOn_logarithmic_decay ((3 : ℝ) / 2) t).mono (Icc_subset_Icc hs le_rfl)).const_mul A
  calc
    _ ≤ ∫ r in s..t, A * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hst _ (hc.intervalIntegrable_of_Icc hst)
      filter_upwards [] with r hr
      exact (norm_heatFlowBUC_le _ _ _).trans (hb r ⟨hr.1.le, hr.2⟩)
    _ = A * ∫ r in s..t, (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r) := by
      simp only [mul_assoc, intervalIntegral.integral_const_mul]
    _ ≤ 32 * A := by nlinarith [integral_logarithmic_decay_subinterval_le hs hst]

end Planarwave
