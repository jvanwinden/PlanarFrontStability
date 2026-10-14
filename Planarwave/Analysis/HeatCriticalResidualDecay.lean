/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingCancellation
public import Planarwave.Analysis.DelayedPolynomialDecay

@[expose] public section

/-!
# Decay of the fully cancelled critical component

Apply the exact tracking cancellation of Step 3b of `lem:key`. After
the first time block, only the most recent two blocks contribute. Thus
the critical component inherits the source's polynomial decay, without
any loss of exponent. The short-time estimate retains the initial datum.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Before the first block is completed, the residual is the remaining
initial pulse mass plus the nonlinear heat response. -/
theorem heatCriticalResidual_initial {a t : ℝ} (ha : 0 ≤ a) (ht : t ∈ Icc (0 : ℝ) 1)
    (p : BUC E F) (N : ℝ → BUC E F) :
    heatFlowBUC a t p + heatDuhamel a N t - heatDuhamel a (delayedHeatForcing a p N) t =
      (1 - ∫ r in (0 : ℝ)..t, trackingCutoff r) • heatFlowBUC a t p + heatDuhamel a N t := by
  have heq : heatDuhamel a (delayedHeatForcing a p N) t =
      heatDuhamel a (fun r ↦ trackingCutoff r • heatFlowBUC a r p) t :=
    heatDuhamel_congr a ht.1 (fun r hr ↦ delayedHeatForcing_initial a p N (hr.2.trans ht.2))
  have hpulse := heatDuhamel_trackingPulse (b := 0) ha ht.1 p
  simp only [sub_zero] at hpulse
  rw [heq, hpulse, sub_smul, one_smul]
  abel

/-- The short-time critical residual is bounded by the initial datum
and the source, with no factor involving the cutoff's supremum norm. -/
theorem norm_heatCriticalResidual_initial_le {a t P M : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Icc (0 : ℝ) 1) (p : BUC E F) (N : ℝ → BUC E F)
    (hp : ‖p‖ ≤ P) (hM : 0 ≤ M) (hN : ∀ r ∈ Icc 0 t, ‖N r‖ ≤ M) :
    ‖heatFlowBUC a t p + heatDuhamel a N t - heatDuhamel a (delayedHeatForcing a p N) t‖ ≤ P + M := by
  have hmass := integral_trackingCutoff_shift_mem (b := 0) ht.1
  simp only [sub_zero] at hmass
  rw [heatCriticalResidual_initial ha ht p N]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hmass.2)]
    calc
      _ ≤ 1 * ‖heatFlowBUC a t p‖ := mul_le_mul_of_nonneg_right (by linarith [hmass.1]) (norm_nonneg _)
      _ ≤ P := by simpa only [one_mul] using (norm_heatFlowBUC_le a t p).trans hp
  · exact (norm_heatDuhamel_le N ht.1 hN).trans ((mul_le_mul_of_nonneg_left ht.2 hM).trans_eq (mul_one M))

/-- After one unit of time, the initial data has cancelled completely.
The polynomial estimate uses only the recent source bound. -/
theorem norm_heatCriticalResidual_decay_late {a γ T M t : ℝ} (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (p : BUC E F) (N : ℝ → BUC E F) (hM : 0 ≤ M)
    (hNc : ContinuousOn N (Icc 0 T)) (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ))
    (ht : t ∈ Icc 1 T) :
    ‖heatFlowBUC a t p + heatDuhamel a N t - heatDuhamel a (delayedHeatForcing a p N) t‖ ≤
      (3 * (3 : ℝ) ^ γ) * M * (1 + t) ^ (-γ) := by
  obtain ⟨n, τ, hτ, rfl⟩ := exists_delayed_time_block ht.1
  have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1 + τ), ‖N r‖ ≤ M * (1 + (n : ℝ)) ^ (-γ) := by
    intro r hr
    exact (hN r ⟨hnn.trans hr.1, hr.2.trans ht.2⟩).trans
      (mul_le_mul_of_nonneg_left (one_add_rpow_neg_antitone hγ hnn hr.1) hM)
  calc
    _ ≤ 3 * (M * (1 + (n : ℝ)) ^ (-γ)) := norm_heatCriticalResidual_le ha p N n hτ
      (hNc.mono (Icc_subset_Icc le_rfl ht.2)) (by positivity) hb
    _ ≤ 3 * (M * ((3 : ℝ) ^ γ * (1 + ((n : ℝ) + 1 + τ)) ^ (-γ))) := by
      apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hM) (by norm_num)
      exact one_add_rpow_neg_le_recent hγ hnn (by linarith [hτ.1]) (by linarith [hτ.2])
    _ = _ := by ring

/-- The estimate `eq:zetaest`, in a form valid for every nonnegative
polynomial exponent. Constants do not depend on the horizon or paths. -/
theorem norm_heatCriticalResidual_decay_le {a γ T M t : ℝ} (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (p : BUC E F) (N : ℝ → BUC E F) (hM : 0 ≤ M) (hp : ‖p‖ ≤ M)
    (hNc : ContinuousOn N (Icc 0 T)) (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ))
    (ht : t ∈ Icc 0 T) :
    ‖heatFlowBUC a t p + heatDuhamel a N t - heatDuhamel a (delayedHeatForcing a p N) t‖ ≤
      (3 * (3 : ℝ) ^ γ) * M * (1 + t) ^ (-γ) := by
  by_cases ht1 : t ≤ 1
  · have hbound : ∀ r ∈ Icc 0 t, ‖N r‖ ≤ M := by
      intro r hr
      have hw := one_add_rpow_neg_antitone hγ (le_refl (0 : ℝ)) hr.1
      simp only [add_zero, Real.one_rpow] at hw
      exact (hN r ⟨hr.1, hr.2.trans ht.2⟩).trans
        ((mul_le_mul_of_nonneg_left hw hM).trans_eq (mul_one M))
    have hw := one_add_rpow_neg_le_recent hγ (le_refl (0 : ℝ)) ht.1 (by linarith : t ≤ 0 + 2)
    simp only [add_zero, Real.one_rpow] at hw
    calc
      _ ≤ M + M := norm_heatCriticalResidual_initial_le ha ⟨ht.1, ht1⟩ p N hp hM hbound
      _ ≤ 3 * M := by linarith
      _ ≤ (3 * M) * ((3 : ℝ) ^ γ * (1 + t) ^ (-γ)) :=
        (mul_one (3 * M)).symm.le.trans (mul_le_mul_of_nonneg_left hw (by positivity))
      _ = _ := by ring
  · exact norm_heatCriticalResidual_decay_late ha hγ p N hM hNc hN ⟨(lt_of_not_ge ht1).le, ht.2⟩

end

end Planarwave
