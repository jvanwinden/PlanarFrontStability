/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingDerivative

@[expose] public section

/-!
# First derivative bounds for the delayed forcing blocks

The fixed positive heat time controls the forcing's actual derivative
using only the initial data or the completed source block. No spatial
derivative of the source occurs, as required in the tracking argument.
-/

open Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem delayedHeatForcingFDeriv_initial {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) {t : ℝ} (ht : t ≤ 1) :
    delayedHeatForcingFDeriv ha p N t = trackingHeatPulseFDeriv ha p t := by
  ext x : 1
  have hd := hasFDerivAt_delayedHeatForcing ha p N t x
  rw [delayedHeatForcing_initial a p N ht] at hd
  exact hd.unique (hasFDerivAt_trackingHeatPulse ha p t x)

theorem delayedHeatForcingFDeriv_block {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (k : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    delayedHeatForcingFDeriv ha p N ((k : ℝ) + 1 + τ) =
      trackingHeatPulseFDeriv ha (delayedHeatBlock a N k) τ := by
  ext x : 1
  have hd := hasFDerivAt_delayedHeatForcing ha p N ((k : ℝ) + 1 + τ) x
  rw [delayedHeatForcing_block a p N k hτ] at hd
  exact hd.unique (hasFDerivAt_trackingHeatPulse ha (delayedHeatBlock a N k) τ x)

/-- On the first time block, both forcing and derivative are controlled
by the undifferentiated initial datum. -/
theorem norm_delayedHeatForcing_c1_initial_le {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) {t : ℝ} (ht : t ≤ 1) :
    max ‖delayedHeatForcing a p N t‖ ‖delayedHeatForcingFDeriv ha p N t‖ ≤
      trackingCutoff t * (max 1 (heatScale a (1 / 8))⁻¹ * ‖p‖) := by
  apply max_le
  · apply (norm_delayedHeatForcing_initial_le a p N ht).trans
    apply mul_le_mul_of_nonneg_left _ (trackingCutoff_nonneg t)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (le_max_left (1 : ℝ) ((heatScale a (1 / 8))⁻¹)) (norm_nonneg p)
  · rw [delayedHeatForcingFDeriv_initial ha p N ht]
    apply (norm_trackingHeatPulseFDeriv_le ha p t).trans
    apply mul_le_mul_of_nonneg_left _ (trackingCutoff_nonneg t)
    rw [div_eq_mul_inv, mul_comm ‖p‖]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg p)

/-- On a later block, the C¹ forcing norm depends only on a supremum
bound for the completed source; no source derivative is required. -/
theorem norm_delayedHeatForcing_c1_block_le {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (k : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ∀ r ∈ Icc (k : ℝ) ((k : ℝ) + 1), ‖N r‖ ≤ M) :
    max ‖delayedHeatForcing a p N ((k : ℝ) + 1 + τ)‖
        ‖delayedHeatForcingFDeriv ha p N ((k : ℝ) + 1 + τ)‖ ≤
      trackingCutoff τ * (max 1 (heatScale a (1 / 8))⁻¹ * M) := by
  have hK : 0 ≤ max 1 (heatScale a (1 / 8))⁻¹ := le_trans (by norm_num) (le_max_left _ _)
  have hbound : max ‖trackingCutoff τ • heatFlowBUC a τ (delayedHeatBlock a N k)‖
        ‖trackingHeatPulseFDeriv ha (delayedHeatBlock a N k) τ‖ ≤
      trackingCutoff τ * (max 1 (heatScale a (1 / 8))⁻¹ * ‖delayedHeatBlock a N k‖) := by
    simpa only [delayedHeatForcing_initial a (delayedHeatBlock a N k) N hτ.2,
      delayedHeatForcingFDeriv_initial ha (delayedHeatBlock a N k) N hτ.2] using
      norm_delayedHeatForcing_c1_initial_le ha (delayedHeatBlock a N k) N hτ.2
  rw [delayedHeatForcing_block a p N k hτ, delayedHeatForcingFDeriv_block ha p N k hτ]
  apply hbound.trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (norm_delayedHeatBlock_le a N k hN) hK) (trackingCutoff_nonneg τ)

end

end Planarwave
