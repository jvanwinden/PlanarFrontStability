/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingRegularity
public import Planarwave.Analysis.DelayedHeatForcingSmoothing

@[expose] public section

/-!
# BUC derivative of the actual delayed forcing

Extract the fixed `1/8` heat factor from each pulse, just as in the paper.
Its differentiated datum is BUC; the remaining heat orbit is continuous
in BUC norm, even as the pulse turns on and off. Local finiteness then
gives a continuous BUC derivative of the complete delayed forcing.
-/

open Filter Set
open scoped Topology

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance delayedForcingDerivativeNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] F)) := inferInstance
local instance delayedForcingDerivativeNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] F)) := inferInstance

/-- The derivative of a cutoff pulse, with a fixed positive-time heat
factor extracted so that the formula is continuous at all times. -/
def trackingHeatPulseFDeriv {a : ℝ} (ha : 0 < a) (f : BUC E F) (t : ℝ) :
    BUC E (E →L[ℝ] F) :=
  trackingCutoff t • heatFlowBUC a (t - 1 / 8)
    (heatFDerivBUC ha (by norm_num : (0 : ℝ) < 1 / 8) f)

theorem continuous_trackingHeatPulseFDeriv {a : ℝ} (ha : 0 < a) (f : BUC E F) :
    Continuous (trackingHeatPulseFDeriv ha f) :=
  trackingCutoff.continuous.smul
    ((continuous_heatFlowBUC_time a (heatFDerivBUC ha (by norm_num : (0 : ℝ) < 1 / 8) f)).comp
      (continuous_id.sub continuous_const))

theorem hasFDerivAt_trackingHeatPulse {a : ℝ} (ha : 0 < a) (f : BUC E F) (t : ℝ) (x : E) :
    HasFDerivAt (trackingCutoff t • heatFlowBUC a t f) (trackingHeatPulseFDeriv ha f t x) x := by
  by_cases hρ : trackingCutoff t = 0
  · simpa [hρ, trackingHeatPulseFDeriv] using!
      hasFDerivAt_const (𝕜 := ℝ) (0 : F) x
  have ht : 0 ≤ t - 1 / 8 := by linarith [(trackingCutoff_ne_zero_mem hρ).1]
  have hsplit : heatFlowBUC a t f = heatFlowBUC a (t - 1 / 8) (heatFlowBUC a (1 / 8) f) := by
    simpa only [sub_add_cancel] using heatFlowBUC_add_apply ha.le ht (by norm_num : (0 : ℝ) ≤ 1 / 8) f
  have hd : ∀ y, HasFDerivAt (heatFlowBUC a (1 / 8) f)
      (heatFDerivBUC ha (by norm_num : (0 : ℝ) < 1 / 8) f y) y := by
    intro y
    simpa only [heatFDerivBUC_apply] using!
      (hasFDerivAt_heatFlow ha (by norm_num : (0 : ℝ) < 1 / 8) f y).differentiableAt.hasFDerivAt
  rw [hsplit]
  simpa only [trackingHeatPulseFDeriv, BUC.smul_apply] using!
    (hasFDerivAt_heatFlow_of_hasFDerivAt a (t - 1 / 8) _ _ hd x).const_smul (trackingCutoff t)

theorem norm_trackingHeatPulseFDeriv_le {a : ℝ} (ha : 0 < a) (f : BUC E F) (t : ℝ) :
    ‖trackingHeatPulseFDeriv ha f t‖ ≤ trackingCutoff t * (‖f‖ / heatScale a (1 / 8)) := by
  rw [trackingHeatPulseFDeriv, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (trackingCutoff_nonneg t)]
  exact mul_le_mul_of_nonneg_left
    ((norm_heatFlowBUC_le _ _ _).trans (norm_heatFDerivBUC_le ha (by norm_num : (0 : ℝ) < 1 / 8) f))
    (trackingCutoff_nonneg t)

/-- The first spatial derivative of the paper's delayed forcing. -/
def delayedHeatForcingFDeriv {a : ℝ} (ha : 0 < a) (p : BUC E F) (N : ℝ → BUC E F)
    (t : ℝ) : BUC E (E →L[ℝ] F) :=
  trackingHeatPulseFDeriv ha p t +
    ∑' k : ℕ, trackingHeatPulseFDeriv ha (delayedHeatBlock a N k) (t - ((k : ℝ) + 1))

theorem delayedHeatForcingFDeriv_eq_sum {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (K : ℕ) {t : ℝ} (ht : t ≤ (K : ℝ) + 1) :
    delayedHeatForcingFDeriv ha p N t = trackingHeatPulseFDeriv ha p t +
      ∑ k ∈ Finset.range K,
        trackingHeatPulseFDeriv ha (delayedHeatBlock a N k) (t - ((k : ℝ) + 1)) := by
  unfold delayedHeatForcingFDeriv
  congr 1
  apply tsum_eq_sum
  intro k hk
  have hkn : K ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hkn
  simp only [trackingHeatPulseFDeriv,
    trackingCutoff_eq_zero_of_le (by linarith : t - ((k : ℝ) + 1) ≤ 1 / 4), zero_smul]

/-- Continuity in the BUC norm, not merely joint pointwise continuity. -/
theorem continuous_delayedHeatForcingFDeriv {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) : Continuous (delayedHeatForcingFDeriv ha p N) := by
  rw [continuous_iff_continuousAt]
  intro t
  let K : ℕ := ⌈t⌉₊ + 1
  have hK : t < (K : ℝ) + 1 := by
    have h := Nat.le_ceil t
    dsimp [K]
    push_cast
    linarith
  have hG : Continuous (fun r ↦ trackingHeatPulseFDeriv ha p r +
      ∑ k ∈ Finset.range K,
        trackingHeatPulseFDeriv ha (delayedHeatBlock a N k) (r - ((k : ℝ) + 1))) := by
    apply (continuous_trackingHeatPulseFDeriv ha p).add
    apply continuous_finsetSum
    intro k _
    exact (continuous_trackingHeatPulseFDeriv ha (delayedHeatBlock a N k)).comp
      (continuous_id.sub continuous_const)
  apply hG.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hK] with r hr
  exact delayedHeatForcingFDeriv_eq_sum ha p N K hr.le

/-- The constructed BUC field is the actual Fréchet derivative of the
delayed forcing, with no spatial differentiability assumption on `N`. -/
theorem hasFDerivAt_delayedHeatForcing {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (t : ℝ) (x : E) :
    HasFDerivAt (delayedHeatForcing a p N t) (delayedHeatForcingFDeriv ha p N t x) x := by
  let K : ℕ := ⌈t⌉₊ + 1
  have hK : t ≤ (K : ℝ) + 1 := by
    have h := Nat.le_ceil t
    dsimp [K]
    push_cast
    linarith
  rw [delayedHeatForcing_eq_sum a p N K hK, delayedHeatForcingFDeriv_eq_sum ha p N K hK]
  have hs := HasFDerivAt.sum (u := Finset.range K)
    (fun k _ ↦ hasFDerivAt_trackingHeatPulse ha (delayedHeatBlock a N k)
      (t - ((k : ℝ) + 1)) x)
  have h := (hasFDerivAt_trackingHeatPulse ha p t x).add hs
  convert! h using 1
  · ext y
    simp only [BUC.add_apply, Pi.add_apply, Finset.sum_apply]
    congr 1
    exact map_sum (BUC.evalCLM (𝕜 := ℝ) y) _ _
  · simp only [BUC.add_apply]
    congr 1
    exact map_sum (BUC.evalCLM (𝕜 := ℝ) x) _ _

end

end Planarwave
