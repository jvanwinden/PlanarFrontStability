/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamel
public import Planarwave.Analysis.HeatSmoothMultidimensional

@[expose] public section

/-!
# The positive-time heat gradient on BUC

The gradient is a bounded linear operator at each positive time. Splitting
off a fixed positive heat age proves joint strong continuity away from zero.
This is the operator-valued integrand needed for parabolic Duhamel smoothing.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The bounded spatial derivative of a positive-time heat operator. -/
def heatFDerivOperator {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    BUC E F →L[ℝ] BUC E (E →L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := heatFDerivBUC ha ht
      map_add' := by
        intro f g
        apply BUC.ext
        intro x
        have hd := (hasFDerivAt_heatFlow ha ht f x).add
          (hasFDerivAt_heatFlow ha ht g x)
        change HasFDerivAt (heatFlowBUC a t f + heatFlowBUC a t g : BUC E F)
          (heatFDerivBUC ha ht f x + heatFDerivBUC ha ht g x) x at hd
        rw [← heatFlowBUC_add] at hd
        exact (hasFDerivAt_heatFlow ha ht (f + g) x).unique hd
      map_smul' := by
        intro c f
        apply BUC.ext
        intro x
        have hd := (hasFDerivAt_heatFlow ha ht f x).const_smul c
        change HasFDerivAt (c • heatFlowBUC a t f : BUC E F)
          (c • heatFDerivBUC ha ht f x) x at hd
        rw [← heatFlowBUC_smul] at hd
        exact (hasFDerivAt_heatFlow ha ht (c • f) x).unique hd }
    (heatScale a t)⁻¹ (fun f ↦ by
      simpa only [div_eq_mul_inv, mul_comm] using! norm_heatFDerivBUC_le ha ht f)

@[simp] theorem heatFDerivOperator_apply {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) : heatFDerivOperator ha ht f = heatFDerivBUC ha ht f := rfl

/-- Extend the heat gradient by zero at nonpositive heat ages. The value at
zero is immaterial to Duhamel integration. -/
def heatGradient {a : ℝ} (ha : 0 < a) (t : ℝ) :
    BUC E F →L[ℝ] BUC E (E →L[ℝ] F) :=
  if ht : 0 < t then heatFDerivOperator ha ht else 0

theorem heatGradient_of_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    heatGradient ha t f = heatFDerivBUC ha ht f := by
  simp [heatGradient, ht]

theorem hasFDerivAt_heatFlow_gradient {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (x : E) :
    HasFDerivAt (heatFlowBUC a t f) (heatGradient ha t f x) x := by
  rw [heatGradient_of_pos ha ht]
  exact hasFDerivAt_heatFlow ha ht f x

theorem norm_heatGradient_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    ‖heatGradient ha t f‖ ≤ ‖f‖ / heatScale a t := by
  rw [heatGradient_of_pos ha ht]
  exact norm_heatFDerivBUC_le ha ht f

/-- Propagate an already smoothed gradient over the remaining heat age. -/
theorem heatGradient_split {a s t : ℝ} (ha : 0 < a) (hs : 0 < s) (hst : s ≤ t)
    (f : BUC E F) :
    heatGradient ha t f = heatFlowBUC a (t - s) (heatGradient ha s f) := by
  have ht : 0 < t := hs.trans_le hst
  have heq : heatFlowBUC a t f = heatFlowBUC a (t - s) (heatFlowBUC a s f) := by
    simpa only [sub_add_cancel] using
      heatFlowBUC_add_apply ha.le (sub_nonneg.mpr hst) hs.le f
  apply BUC.ext
  intro x
  have hd := hasFDerivAt_heatFlow_of_hasFDerivAt a (t - s) (heatFlowBUC a s f)
    (heatGradient ha s f) (hasFDerivAt_heatFlow_gradient ha hs f) x
  have hd' := hasFDerivAt_heatFlow_gradient ha ht f x
  rw [heq] at hd'
  exact hd'.unique hd

/-- Joint strong continuity on strictly positive heat ages. No operator-norm
continuity at zero, nor differentiability of the datum, is required. -/
theorem continuousOn_heatGradient_joint {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × BUC E F ↦ heatGradient ha p.1 p.2)
      (Ioi 0 ×ˢ univ) := by
  intro p hp
  have hp0 : 0 < p.1 := hp.1
  have hs : 0 < p.1 / 2 := by linarith
  have hc : Continuous (fun q : ℝ × BUC E F ↦
      heatFlowBUC a (q.1 - p.1 / 2) (heatGradient ha (p.1 / 2) q.2)) :=
    (continuous_heatFlowBUC_joint a).comp
      ((continuous_fst.sub continuous_const).prodMk
        ((heatGradient ha (p.1 / 2)).continuous.comp continuous_snd))
  apply ContinuousAt.continuousWithinAt
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually
    (lt_mem_nhds (show p.1 / 2 < p.1 by linarith))] with q hq
  exact heatGradient_split ha hs hq.le q.2

end

end Planarwave
