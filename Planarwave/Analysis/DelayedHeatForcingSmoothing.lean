/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcing

@[expose] public section

/-!
# The fixed smoothing factor in the delayed forcing

Because every nonzero pulse has age greater than `1/4`, a heat factor of age
`1/8` can always be moved onto its source. This is the precise interface
between the delayed forcing and the derivative-free estimate of Lemma 4.2.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Strong heat continuity plus its uniform contraction bound gives joint continuity. -/
theorem continuous_heatFlowBUC_joint (a : ℝ) :
    Continuous (fun p : ℝ × BUC E F ↦ heatFlowBUC a p.1 p.2) := by
  have h : ContinuousOn (fun p : ℝ × BUC E F ↦ heatFlowBUC a p.1 p.2) (univ ×ˢ univ) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ 1
    · intro t _
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le
        (K := 1) (norm_heatOperator_le (E := E) (F := F) a t)).lipschitzOnWith
    · intro f _
      exact (continuous_heatFlowBUC_time a f).continuousOn
  simpa only [univ_prod_univ, continuousOn_univ] using h

theorem heatFlowBUC_add_apply {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : BUC E F) : heatFlowBUC a (s + t) f = heatFlowBUC a s (heatFlowBUC a t f) := by
  exact (congrArg (fun L : BUC E F →L[ℝ] BUC E F ↦ L f) (heatOperator_add_time ha hs ht)).symm

theorem intervalIntegrable_delayedHeatBlock (a : ℝ) (N : ℝ → BUC E F) (n : ℕ)
    (hN : ContinuousOn N (Icc (n : ℝ) ((n : ℝ) + 1))) :
    IntervalIntegrable (fun r ↦ heatFlowBUC a ((n : ℝ) + 1 - r) (N r)) volume
      (n : ℝ) ((n : ℝ) + 1) :=
  ((continuous_heatFlowBUC_joint a).comp_continuousOn
    ((continuousOn_const.sub continuousOn_id).prodMk hN)).intervalIntegrable_of_Icc (by linarith)

/-- A fixed heat factor commutes through the accumulated preceding block. -/
theorem heatFlowBUC_delayedHeatBlock {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (N : ℝ → BUC E F) (n : ℕ) (hN : ContinuousOn N (Icc (n : ℝ) ((n : ℝ) + 1))) :
    heatFlowBUC a ε (delayedHeatBlock a N n) =
      delayedHeatBlock a (fun r ↦ heatFlowBUC a ε (N r)) n := by
  change (heatOperator a ε) (∫ r in (n : ℝ)..(n : ℝ) + 1,
    heatFlowBUC a ((n : ℝ) + 1 - r) (N r)) = _
  rw [← (heatOperator a ε).intervalIntegral_comp_comm (intervalIntegrable_delayedHeatBlock a N n hN)]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hr
  have htime : 0 ≤ (n : ℝ) + 1 - r := sub_nonneg.mpr hr.2
  change heatFlowBUC a ε (heatFlowBUC a ((n : ℝ) + 1 - r) (N r)) =
    heatFlowBUC a ((n : ℝ) + 1 - r) (heatFlowBUC a ε (N r))
  rw [← heatFlowBUC_add_apply ha hε htime, ← heatFlowBUC_add_apply ha htime hε, add_comm]

/-- The paper's `1/8` smoothing factor is extracted as an exact identity.
Outside the pulse support, both sides vanish. -/
theorem delayedHeatForcing_block_smoothed {a : ℝ} (ha : 0 ≤ a)
    (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (n : ℝ) ((n : ℝ) + 1))) :
    delayedHeatForcing a p N ((n : ℝ) + 1 + τ) =
      trackingCutoff τ • heatFlowBUC a (τ - 1 / 8)
        (delayedHeatBlock a (fun r ↦ heatFlowBUC a (1 / 8) (N r)) n) := by
  rw [delayedHeatForcing_block a p N n hτ]
  by_cases hρ : trackingCutoff τ = 0
  · simp only [hρ, zero_smul]
  have htime : 0 ≤ τ - 1 / 8 := by linarith [(trackingCutoff_ne_zero_mem hρ).1]
  have hsplit (b : BUC E F) : heatFlowBUC a τ b =
      heatFlowBUC a (τ - 1 / 8) (heatFlowBUC a (1 / 8) b) := by
    simpa only [sub_add_cancel] using heatFlowBUC_add_apply ha htime (by norm_num : (0 : ℝ) ≤ 1 / 8) b
  rw [hsplit, heatFlowBUC_delayedHeatBlock ha (by norm_num) N n hN]

/-- The delayed forcing is bounded using only the smoothed source. This
removes the spatial derivative norms of the perturbation after Lemma 4.2. -/
theorem norm_delayedHeatForcing_block_smoothed_le {a : ℝ} (ha : 0 ≤ a)
    (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (n : ℝ) ((n : ℝ) + 1)))
    (hbound : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1), ‖heatFlowBUC a (1 / 8) (N r)‖ ≤ M) :
    ‖delayedHeatForcing a p N ((n : ℝ) + 1 + τ)‖ ≤ trackingCutoff τ * M := by
  rw [delayedHeatForcing_block_smoothed ha p N n hτ hN, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (trackingCutoff_nonneg τ)]
  exact mul_le_mul_of_nonneg_left
    ((norm_heatFlowBUC_le _ _ _).trans (norm_delayedHeatBlock_le a _ n hbound))
    (trackingCutoff_nonneg τ)

end

end Planarwave
