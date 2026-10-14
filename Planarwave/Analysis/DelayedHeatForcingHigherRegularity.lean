/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialRegularity
public import Planarwave.Analysis.DelayedHeatForcingDerivative

@[expose] public section

/-!
# BUC time continuity of every delayed-forcing spatial derivative

Reserve a positive heat interval before differentiating a pulse. Iterating
this construction keeps a positive heat age on the cutoff support. Each
derivative remains a heat orbit of fixed BUC data, hence is continuous in
time in BUC norm. Finite sums give the actual forcing on every finite horizon.
-/

open Set

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance higherPulseCLMNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance higherPulseCLMNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance higherPulseBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] F)) := inferInstance

/-- Every cutoff heat pulse has BUC derivatives of all orders, continuously
in time. The shift `s < 1/4` records the heat intervals already extracted. -/
theorem bucSpatialRegularOn_trackingHeatPulse_shift (k : ℕ) {a : ℝ} (ha : 0 < a)
    (f : BUC E F) {s : ℝ} (hs : s < 1 / 4) :
    BUCSpatialRegularOn univ k (fun t ↦ trackingCutoff t • heatFlowBUC a (t - s) f) := by
  induction k generalizing F s with
  | zero =>
    exact (trackingCutoff.continuous.smul
      ((continuous_heatFlowBUC_time a f).comp (continuous_id.sub continuous_const))).continuousOn
  | succ k ih =>
    let ε := (1 / 4 - s) / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    have hs' : s + ε < 1 / 4 := by dsimp only [ε]; linarith
    let g := heatFDerivBUC ha hε f
    refine ⟨(trackingCutoff.continuous.smul
      ((continuous_heatFlowBUC_time a f).comp (continuous_id.sub continuous_const))).continuousOn,
      fun t ↦ trackingCutoff t • heatFlowBUC a (t - (s + ε)) g, ih g hs', ?_⟩
    intro t _ x
    dsimp only
    by_cases hρ : trackingCutoff t = 0
    · simpa only [hρ, zero_smul, BUC.coe_zero, BUC.zero_apply] using!
        hasFDerivAt_const (𝕜 := ℝ) (0 : F) x
    have hrest : 0 ≤ t - (s + ε) := by linarith [(trackingCutoff_ne_zero_mem hρ).1]
    have hsplit : heatFlowBUC a (t - s) f =
        heatFlowBUC a (t - (s + ε)) (heatFlowBUC a ε f) := by
      convert heatFlowBUC_add_apply ha.le hrest hε.le f using 1
      congr 1
      ring
    have hd : ∀ y, HasFDerivAt (heatFlowBUC a ε f) (g y) y :=
      fun y ↦ hasFDerivAt_heatFlow ha hε f y
    rw [hsplit]
    simpa only [BUC.smul_apply] using!
      (hasFDerivAt_heatFlow_of_hasFDerivAt a (t - (s + ε)) _ _ hd x).const_smul (trackingCutoff t)

/-- All spatial derivatives of the full delayed forcing are continuous as
BUC-valued paths on any finite horizon. No source regularity is assumed. -/
theorem bucSpatialRegularOn_delayedHeatForcing (k : ℕ) {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (T : ℝ) :
    BUCSpatialRegularOn (Icc 0 T) k (delayedHeatForcing a p N) := by
  let K : ℕ := ⌈T⌉₊ + 1
  have hK : T ≤ (K : ℝ) + 1 := by
    have h := Nat.le_ceil T
    dsimp only [K]
    push_cast
    linarith
  have hpulse (b : BUC E F) :
      BUCSpatialRegularOn univ k (fun t ↦ trackingCutoff t • heatFlowBUC a t b) := by
    simpa only [sub_zero] using bucSpatialRegularOn_trackingHeatPulse_shift k ha b
      (by norm_num : (0 : ℝ) < 1 / 4)
  have hsum := BUCSpatialRegularOn.sum (Finset.range K) (fun n _ ↦
    (hpulse (delayedHeatBlock a N n)).comp_time (r := fun t ↦ t - ((n : ℝ) + 1))
      (continuous_id.sub continuous_const))
  apply ((hpulse p).add hsum).mono (subset_univ _) |>.congr
  intro t ht
  exact (delayedHeatForcing_eq_sum a p N K (ht.2.trans hK)).symm

end

end Planarwave
