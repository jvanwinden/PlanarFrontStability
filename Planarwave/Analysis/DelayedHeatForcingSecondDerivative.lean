/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingDerivative
public import Planarwave.Analysis.ConvectiveHeatSmoothingMultidimensional

@[expose] public section

/-!
# A second BUC derivative of the delayed forcing

The fixed positive-time heat factor in each delayed pulse has two BUC
derivatives. Propagation of that fixed second derivative proves continuity
in the BUC norm, including at the boundaries of the temporal cutoffs.
-/

open Filter Set
open scoped Topology

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_buc_fderivative_heatFDerivBUC {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) : ∃ h : BUC E (E →L[ℝ] E →L[ℝ] F),
      ∀ x, HasFDerivAt (heatFDerivBUC ha ht f) (h x) x := by
  obtain ⟨g, h, hg, hh⟩ := exists_buc_fderivatives_heatFlow ha ht f
  have heq : g = heatFDerivBUC ha ht f := by
    ext x : 1
    exact (hg x).unique (hasFDerivAt_heatFlow ha ht f x)
  exact ⟨h, fun x ↦ heq ▸ hh x⟩

/-- A BUC second derivative of a positive-time heat orbit. -/
def heatSecondFDerivBUC {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    BUC E (E →L[ℝ] E →L[ℝ] F) := (exists_buc_fderivative_heatFDerivBUC ha ht f).choose

theorem hasFDerivAt_heatFDerivBUC {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (x : E) :
    HasFDerivAt (heatFDerivBUC ha ht f) (heatSecondFDerivBUC ha ht f x) x :=
  (exists_buc_fderivative_heatFDerivBUC ha ht f).choose_spec x

local instance delayedForcingSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] E →L[ℝ] F)
local instance delayedForcingSecondDerivativeNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] F)) :=
  BUC.instNormedSpace (𝕜 := ℝ) (α := E) (E := E →L[ℝ] E →L[ℝ] F)

/-- The chosen second derivative has the dimension-independent heat bound. -/
theorem norm_heatSecondFDerivBUC_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    ‖heatSecondFDerivBUC ha ht f‖ ≤ ‖f‖ / (a * t) := by
  obtain ⟨g, h, hg, hh, _, hbound⟩ := exists_bounded_buc_fderivatives_heatFlow ha ht f
  have hgeq : g = heatFDerivBUC ha ht f := by
    ext x : 1
    exact (hg x).unique (hasFDerivAt_heatFlow ha ht f x)
  have hheq : h = heatSecondFDerivBUC ha ht f := by
    ext x : 1
    exact (hgeq ▸ hh x).unique (hasFDerivAt_heatFDerivBUC ha ht f x)
  rwa [hheq] at hbound

def trackingHeatPulseFDeriv2 {a : ℝ} (ha : 0 < a) (f : BUC E F) (t : ℝ) :
    BUC E (E →L[ℝ] E →L[ℝ] F) :=
  trackingCutoff t • heatFlowBUC (E := E) (F := E →L[ℝ] E →L[ℝ] F) a (t - 1 / 8)
    (heatSecondFDerivBUC ha (by norm_num : (0 : ℝ) < 1 / 8) f)

theorem continuous_trackingHeatPulseFDeriv2 {a : ℝ} (ha : 0 < a) (f : BUC E F) :
    Continuous (trackingHeatPulseFDeriv2 ha f) := by
  have hc := (continuous_heatFlowBUC_time (E := E) (F := E →L[ℝ] E →L[ℝ] F) a
    (heatSecondFDerivBUC ha (by norm_num : (0 : ℝ) < 1 / 8) f)).comp
      (continuous_id.sub (continuous_const (y := (1 / 8 : ℝ))))
  exact trackingCutoff.continuous.smul hc

theorem hasFDerivAt_trackingHeatPulseFDeriv {a : ℝ} (ha : 0 < a)
    (f : BUC E F) (t : ℝ) (x : E) :
    HasFDerivAt (trackingHeatPulseFDeriv ha f t) (trackingHeatPulseFDeriv2 ha f t x) x := by
  simpa only [trackingHeatPulseFDeriv, trackingHeatPulseFDeriv2, BUC.smul_apply] using!
    (hasFDerivAt_heatFlow_of_hasFDerivAt (E := E) (F := E →L[ℝ] F) a (t - 1 / 8) _ _
      (hasFDerivAt_heatFDerivBUC ha (by norm_num : (0 : ℝ) < 1 / 8) f) x).const_smul (trackingCutoff t)

/-- A pulse's second derivative is bounded by its undifferentiated datum,
using the fixed positive heat age, uniformly in the pulse time. -/
theorem norm_trackingHeatPulseFDeriv2_le {a : ℝ} (ha : 0 < a) (f : BUC E F) (t : ℝ) :
    ‖trackingHeatPulseFDeriv2 ha f t‖ ≤ trackingCutoff t * (‖f‖ / (a * (1 / 8))) := by
  rw [trackingHeatPulseFDeriv2, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (trackingCutoff_nonneg t)]
  exact mul_le_mul_of_nonneg_left
    ((norm_heatFlowBUC_le _ _ _).trans
      (norm_heatSecondFDerivBUC_le ha (by norm_num : (0 : ℝ) < 1 / 8) f))
    (trackingCutoff_nonneg t)

def delayedHeatForcingFDeriv2 {a : ℝ} (ha : 0 < a) (p : BUC E F) (N : ℝ → BUC E F)
    (t : ℝ) : BUC E (E →L[ℝ] E →L[ℝ] F) :=
  trackingHeatPulseFDeriv2 ha p t +
    ∑' k : ℕ, trackingHeatPulseFDeriv2 ha (delayedHeatBlock a N k) (t - ((k : ℝ) + 1))

theorem delayedHeatForcingFDeriv2_eq_sum {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (K : ℕ) {t : ℝ} (ht : t ≤ (K : ℝ) + 1) :
    delayedHeatForcingFDeriv2 ha p N t = trackingHeatPulseFDeriv2 ha p t +
      ∑ k ∈ Finset.range K,
        trackingHeatPulseFDeriv2 ha (delayedHeatBlock a N k) (t - ((k : ℝ) + 1)) := by
  unfold delayedHeatForcingFDeriv2
  congr 1
  apply tsum_eq_sum
  intro k hk
  have hkn : K ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hkn
  simp only [trackingHeatPulseFDeriv2,
    trackingCutoff_eq_zero_of_le (by linarith : t - ((k : ℝ) + 1) ≤ 1 / 4), zero_smul]

theorem continuous_delayedHeatForcingFDeriv2 {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) : Continuous (delayedHeatForcingFDeriv2 ha p N) := by
  rw [continuous_iff_continuousAt]
  intro t
  let K : ℕ := ⌈t⌉₊ + 1
  have hK : t < (K : ℝ) + 1 := by
    have h := Nat.le_ceil t
    dsimp [K]
    push_cast
    linarith
  have hG : Continuous (fun r ↦ trackingHeatPulseFDeriv2 ha p r +
      ∑ k ∈ Finset.range K,
        trackingHeatPulseFDeriv2 ha (delayedHeatBlock a N k) (r - ((k : ℝ) + 1))) := by
    apply (continuous_trackingHeatPulseFDeriv2 ha p).add
    apply continuous_finsetSum
    intro k _
    exact (continuous_trackingHeatPulseFDeriv2 ha (delayedHeatBlock a N k)).comp
      (continuous_id.sub continuous_const)
  apply hG.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hK] with r hr
  exact delayedHeatForcingFDeriv2_eq_sum ha p N K hr.le

/-- The actual first derivative of the delayed forcing has a second BUC
derivative, without differentiability assumptions on the source. -/
theorem hasFDerivAt_delayedHeatForcingFDeriv {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (t : ℝ) (x : E) :
    HasFDerivAt (delayedHeatForcingFDeriv ha p N t) (delayedHeatForcingFDeriv2 ha p N t x) x := by
  let K : ℕ := ⌈t⌉₊ + 1
  have hK : t ≤ (K : ℝ) + 1 := by
    have h := Nat.le_ceil t
    dsimp [K]
    push_cast
    linarith
  rw [delayedHeatForcingFDeriv_eq_sum ha p N K hK, delayedHeatForcingFDeriv2_eq_sum ha p N K hK]
  have hs := HasFDerivAt.sum (u := Finset.range K)
    (fun k _ ↦ hasFDerivAt_trackingHeatPulseFDeriv ha (delayedHeatBlock a N k)
      (t - ((k : ℝ) + 1)) x)
  have h := (hasFDerivAt_trackingHeatPulseFDeriv ha p t x).add hs
  convert! h using 1
  · funext y
    simp only [BUC.add_apply, Pi.add_apply, Finset.sum_apply]
    congr 1
    exact map_sum (BUC.evalCLM (𝕜 := ℝ) (E := E →L[ℝ] F) y) _ _
  · change (trackingHeatPulseFDeriv2 ha p t) x +
        (∑ k ∈ Finset.range K,
          trackingHeatPulseFDeriv2 ha (delayedHeatBlock a N k) (t - ((k : ℝ) + 1))) x =
      (trackingHeatPulseFDeriv2 ha p t) x +
        ∑ k ∈ Finset.range K,
          trackingHeatPulseFDeriv2 ha (delayedHeatBlock a N k) (t - ((k : ℝ) + 1)) x
    exact congrArg (fun v : E →L[ℝ] E →L[ℝ] F ↦ trackingHeatPulseFDeriv2 ha p t x + v)
      (map_sum (BUC.evalCLM (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] F) x) _ _)

end

end Planarwave
