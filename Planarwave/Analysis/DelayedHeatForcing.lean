/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.TemporalCutoff
public import Planarwave.Analysis.HeatSemigroup

@[expose] public section

/-!
# The delayed forcing of Section 4.2

The natural index `k` below represents the paper's positive integer `k+1`.
Only the preceding unit time interval enters each forcing pulse. The source
will be the adjoint projection of the front's nonlinear remainder.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The source accumulated during a single completed time block. -/
def delayedHeatBlock (a : ℝ) (N : ℝ → BUC E F) (k : ℕ) : BUC E F :=
  ∫ r in (k : ℝ)..(k : ℝ) + 1, heatFlowBUC a ((k : ℝ) + 1 - r) (N r)

/-- Equation `eq:defgnew`, including the initial-data pulse. -/
def delayedHeatForcing (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F) (t : ℝ) : BUC E F :=
  trackingCutoff t • heatFlowBUC a t p +
    ∑' k : ℕ, trackingCutoff (t - ((k : ℝ) + 1)) •
      heatFlowBUC a (t - ((k : ℝ) + 1)) (delayedHeatBlock a N k)

/-- On one unit interval, all the other pulses vanish, including at endpoints. -/
theorem trackingCutoff_shift_ne (n k : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hk : k ≠ n) : trackingCutoff ((n : ℝ) + 1 + τ - ((k : ℝ) + 1)) = 0 := by
  rcases lt_or_gt_of_ne hk with hkn | hnk
  · have hcast : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    apply trackingCutoff_eq_zero_of_ge
    linarith [hτ.1]
  · have hcast : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
    apply trackingCutoff_eq_zero_of_le
    linarith [hτ.2]

/-- Before the first completed source block, forcing consists only of initial data. -/
theorem delayedHeatForcing_initial (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F)
    {t : ℝ} (ht : t ≤ 1) :
    delayedHeatForcing a p N t = trackingCutoff t • heatFlowBUC a t p := by
  have hzero (k : ℕ) : trackingCutoff (t - ((k : ℝ) + 1)) = 0 :=
    trackingCutoff_eq_zero_of_le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  simp only [delayedHeatForcing, hzero, zero_smul, tsum_zero, add_zero]

/-- The forcing vanishes on the whole initial quarter-unit interval. -/
theorem delayedHeatForcing_eq_zero_of_le_quarter (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F)
    {t : ℝ} (ht : t ≤ 1 / 4) : delayedHeatForcing a p N t = 0 := by
  rw [delayedHeatForcing_initial a p N (by linarith), trackingCutoff_eq_zero_of_le ht, zero_smul]

/-- On every bounded-above time interval the defining series is a fixed
finite sum. This justifies regularity without any summability hypothesis. -/
theorem delayedHeatForcing_eq_sum (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F)
    (K : ℕ) {t : ℝ} (ht : t ≤ (K : ℝ) + 1) :
    delayedHeatForcing a p N t = trackingCutoff t • heatFlowBUC a t p +
      ∑ k ∈ Finset.range K, trackingCutoff (t - ((k : ℝ) + 1)) •
        heatFlowBUC a (t - ((k : ℝ) + 1)) (delayedHeatBlock a N k) := by
  unfold delayedHeatForcing
  congr 1
  apply tsum_eq_sum
  intro k hk
  have hkn : K ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hkn
  rw [trackingCutoff_eq_zero_of_le (by linarith : t - ((k : ℝ) + 1) ≤ 1 / 4), zero_smul]

/-- The exact block formula: no values of the source after `n+1` occur. -/
theorem delayedHeatForcing_block (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F)
    (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    delayedHeatForcing a p N ((n : ℝ) + 1 + τ) =
      trackingCutoff τ • heatFlowBUC a τ (delayedHeatBlock a N n) := by
  have hinit : trackingCutoff ((n : ℝ) + 1 + τ) = 0 :=
    trackingCutoff_eq_zero_of_ge (by have := Nat.cast_nonneg (α := ℝ) n; linarith [hτ.1])
  rw [delayedHeatForcing, hinit, zero_smul, zero_add,
    tsum_eq_single n (fun k hk ↦ by rw [trackingCutoff_shift_ne n k hτ hk, zero_smul])]
  congr 2 <;> ring

/-- The block only depends on the source on its own integration interval. -/
theorem delayedHeatBlock_congr (a : ℝ) {N M : ℝ → BUC E F} (n : ℕ)
    (h : EqOn N M (Icc (n : ℝ) ((n : ℝ) + 1))) :
    delayedHeatBlock a N n = delayedHeatBlock a M n := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hr
  dsimp only
  rw [h hr]

/-- The causality needed for the paper's blockwise nonlinear iteration:
forcing on `[n,n+1]` uses only source values on `[0,n]`. -/
theorem delayedHeatForcing_causal (a : ℝ) (p : BUC E F) {N M : ℝ → BUC E F}
    (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (h : EqOn N M (Icc (0 : ℝ) (n : ℝ))) :
    delayedHeatForcing a p N ((n : ℝ) + τ) = delayedHeatForcing a p M ((n : ℝ) + τ) := by
  cases n with
  | zero => simp only [Nat.cast_zero, zero_add, delayedHeatForcing_initial a p _ hτ.2]
  | succ n =>
    simp only [Nat.cast_succ, delayedHeatForcing_block a p _ n hτ]
    rw [delayedHeatBlock_congr a n (fun r hr ↦ h ⟨(Nat.cast_nonneg n).trans hr.1, by
      simpa only [Nat.cast_succ] using hr.2⟩)]

/-- A uniform source bound on one unit block bounds its accumulated heat evolution. -/
theorem norm_delayedHeatBlock_le (a : ℝ) (N : ℝ → BUC E F) (n : ℕ) {M : ℝ}
    (hN : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1), ‖N r‖ ≤ M) :
    ‖delayedHeatBlock a N n‖ ≤ M := by
  have hb : ∀ r ∈ uIoc (n : ℝ) ((n : ℝ) + 1),
      ‖heatFlowBUC a ((n : ℝ) + 1 - r) (N r)‖ ≤ M := by
    intro r hr
    rw [uIoc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hr
    exact (norm_heatFlowBUC_le _ _ _).trans (hN r ⟨hr.1.le, hr.2⟩)
  simpa only [delayedHeatBlock, add_sub_cancel_left, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem norm_delayedHeatForcing_initial_le (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F)
    {t : ℝ} (ht : t ≤ 1) :
    ‖delayedHeatForcing a p N t‖ ≤ trackingCutoff t * ‖p‖ := by
  rw [delayedHeatForcing_initial a p N ht, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (trackingCutoff_nonneg t)]
  exact mul_le_mul_of_nonneg_left (norm_heatFlowBUC_le _ _ _) (trackingCutoff_nonneg t)

/-- The basic supremum bound for the delayed forcing, before using Lemma 4.2. -/
theorem norm_delayedHeatForcing_block_le (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F)
    (n : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1), ‖N r‖ ≤ M) :
    ‖delayedHeatForcing a p N ((n : ℝ) + 1 + τ)‖ ≤ trackingCutoff τ * M := by
  rw [delayedHeatForcing_block a p N n hτ, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (trackingCutoff_nonneg τ)]
  exact mul_le_mul_of_nonneg_left
    ((norm_heatFlowBUC_le _ _ _).trans (norm_delayedHeatBlock_le a N n hN))
    (trackingCutoff_nonneg τ)

end

end Planarwave
