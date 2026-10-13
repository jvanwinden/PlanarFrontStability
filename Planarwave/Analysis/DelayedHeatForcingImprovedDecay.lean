/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingSmoothing
public import Planarwave.Analysis.LogarithmicDecayWeights

@[expose] public section

/-!
# Improved decay from a smoothed source

The support of each delayed pulse leaves a heat factor of age `1/8`
on its source. A logarithmically weighted bound on that smoothed source
therefore transfers to the actual forcing. The initial-data pulse is
retained explicitly, as in `eq:gbetterest`.
-/

open Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A smoothed nonlinear bound gives the improved forcing bound, with
the original initial pulse unchanged. Only completed blocks are used. -/
theorem norm_delayedHeatForcing_improved_decay_le {a γ A T : ℝ}
    (ha : 0 ≤ a) (hγ : 0 ≤ γ) (hA : 0 ≤ A)
    (p : BUC E F) (N : ℝ → BUC E F) (hN : ContinuousOn N (Icc 0 T))
    (hb : ∀ r ∈ Icc 0 T, ‖heatFlowBUC a (1 / 8) (N r)‖ ≤
      A * (1 + r) ^ (-γ) * Real.log (2 + r)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖delayedHeatForcing a p N t‖ ≤ trackingCutoff t * ‖p‖ +
      (‖trackingCutoff‖ * (3 : ℝ) ^ γ) * A * (1 + t) ^ (-γ) * Real.log (2 + t) := by
  have hweight : 0 ≤ (1 + t) ^ (-γ) * Real.log (2 + t) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [ht.1]) _) (Real.log_nonneg (by linarith [ht.1]))
  by_cases ht1 : t ≤ 1
  · apply (norm_delayedHeatForcing_initial_le a p N ht1).trans
    exact le_add_of_nonneg_right (by
      have hpow : 0 ≤ (3 : ℝ) ^ γ := Real.rpow_nonneg (by norm_num) _
      rw [mul_assoc ((‖trackingCutoff‖ * (3 : ℝ) ^ γ) * A)]
      positivity)
  · obtain ⟨k, τ, hτ, htime⟩ := exists_delayed_time_block (le_of_lt (lt_of_not_ge ht1))
    have hblock : Icc (k : ℝ) ((k : ℝ) + 1) ⊆ Icc 0 T := by
      intro r hr
      exact ⟨(Nat.cast_nonneg k).trans hr.1, by linarith [hr.2, hτ.1, ht.2]⟩
    have hb' : ∀ r ∈ Icc (k : ℝ) ((k : ℝ) + 1), ‖heatFlowBUC a (1 / 8) (N r)‖ ≤
        A * ((3 : ℝ) ^ γ * ((1 + t) ^ (-γ) * Real.log (2 + t))) := by
      intro r hr
      have hr0 := (Nat.cast_nonneg k).trans hr.1
      have hrt : r ≤ t := by linarith [hr.2, hτ.1]
      have htr : t ≤ r + 2 := by linarith [hr.1, hτ.2]
      calc
        _ ≤ A * ((1 + r) ^ (-γ) * Real.log (2 + r)) := by simpa only [mul_assoc] using hb r (hblock hr)
        _ ≤ _ := mul_le_mul_of_nonneg_left (logarithmic_decay_le_recent hγ hr0 hrt htr) hA
    have hforce := norm_delayedHeatForcing_block_smoothed_le ha p N k hτ (hN.mono hblock) hb'
    rw [← htime] at hforce
    rw [trackingCutoff_eq_zero_of_ge (by linarith : (3 : ℝ) / 4 ≤ t), zero_mul, zero_add]
    calc
      _ ≤ trackingCutoff τ * (A * ((3 : ℝ) ^ γ * ((1 + t) ^ (-γ) * Real.log (2 + t)))) := hforce
      _ ≤ ‖trackingCutoff‖ * (A * ((3 : ℝ) ^ γ * ((1 + t) ^ (-γ) * Real.log (2 + t)))) :=
        mul_le_mul_of_nonneg_right (trackingCutoff_le_norm τ)
          (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hweight))
      _ = _ := by ring

end

end Planarwave
