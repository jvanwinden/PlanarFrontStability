/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcing
public import Planarwave.Analysis.HeatJointSmoothMultidimensional

@[expose] public section

/-!
# Regularity of the delayed forcing

Each completed block is a fixed BUC datum for a positive-time heat pulse.
The smooth cutoff suppresses the heat flow near age zero, and the defining
series is locally a finite sum. Thus the forcing is jointly smooth, without
requiring time derivatives of the nonlinear source.
-/

open Filter Set
open scoped ContDiff Topology

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A cutoff heat pulse is smooth even across age zero, where it vanishes. -/
theorem contDiff_trackingHeatPulse {a : ℝ} (ha : 0 < a) (f : BUC E F) :
    ContDiff ℝ ∞ (fun q : ℝ × E ↦ trackingCutoff q.1 • heatFlow a q.1 f q.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : 0 < q.1
  · exact (contDiff_trackingCutoff.comp contDiff_fst).contDiffAt.smul
      ((contDiffOn_infty_heatFlow_uncurry ha f).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hq, mem_univ q.2⟩))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto q).eventually
      (Iio_mem_nhds (show q.1 < (1 / 4 : ℝ) by linarith))] with w hw
    simp only [trackingCutoff_eq_zero_of_le hw.le, zero_smul]

/-- Joint smoothness of the complete delayed forcing. This uses no
regularity of the source in time: its completed blocks are fixed BUC data. -/
theorem contDiff_delayedHeatForcing {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) :
    ContDiff ℝ ∞ (fun q : ℝ × E ↦ delayedHeatForcing a p N q.1 q.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  let K : ℕ := ⌈q.1⌉₊ + 1
  have hK : q.1 < (K : ℝ) + 1 := by
    have h := Nat.le_ceil q.1
    dsimp [K]
    push_cast
    linarith
  let G : ℝ × E → F := fun w ↦ trackingCutoff w.1 • heatFlow a w.1 p w.2 +
    ∑ k ∈ Finset.range K, trackingCutoff (w.1 - ((k : ℝ) + 1)) •
      heatFlow a (w.1 - ((k : ℝ) + 1)) (delayedHeatBlock a N k) w.2
  have hG : ContDiff ℝ ∞ G := by
    apply (contDiff_trackingHeatPulse ha p).add
    apply ContDiff.sum
    intro k _
    exact (contDiff_trackingHeatPulse ha (delayedHeatBlock a N k)).comp
      ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  apply hG.contDiffAt.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto q).eventually (Iio_mem_nhds hK)] with w hw
  rw [delayedHeatForcing_eq_sum a p N K hw.le]
  simp only [G, BUC.add_apply, BUC.smul_apply, heatFlowBUC_apply]
  congr 1
  simpa only [BUC.evalCLM_apply, BUC.smul_apply, heatFlowBUC_apply] using
    map_sum (BUC.evalCLM (𝕜 := ℝ) w.2)
      (fun k : ℕ ↦ trackingCutoff (w.1 - ((k : ℝ) + 1)) •
        heatFlowBUC a (w.1 - ((k : ℝ) + 1)) (delayedHeatBlock a N k)) (Finset.range K)

/-- The forcing is continuous as a BUC-valued time path, not merely pointwise. -/
theorem continuous_delayedHeatForcing (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F) :
    Continuous (delayedHeatForcing a p N) := by
  rw [continuous_iff_continuousAt]
  intro t
  let K : ℕ := ⌈t⌉₊ + 1
  have hK : t < (K : ℝ) + 1 := by
    have h := Nat.le_ceil t
    dsimp [K]
    push_cast
    linarith
  have hG : Continuous (fun r ↦ trackingCutoff r • heatFlowBUC a r p +
      ∑ k ∈ Finset.range K, trackingCutoff (r - ((k : ℝ) + 1)) •
        heatFlowBUC a (r - ((k : ℝ) + 1)) (delayedHeatBlock a N k)) := by
    apply (trackingCutoff.continuous.smul (continuous_heatFlowBUC_time a p)).add
    apply continuous_finsetSum
    intro k _
    exact (trackingCutoff.continuous.comp (continuous_id.sub continuous_const)).smul
      ((continuous_heatFlowBUC_time a (delayedHeatBlock a N k)).comp
        (continuous_id.sub continuous_const))
  apply hG.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hK] with r hr
  exact delayedHeatForcing_eq_sum a p N K hr.le

end

end Planarwave
