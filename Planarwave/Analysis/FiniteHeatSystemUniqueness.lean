/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.FiniteHeatSystemLocalExistence
public import Planarwave.Analysis.NonlinearVolterraUniqueness

@[expose] public section

/-!
# Uniqueness for finite coupled heat systems

Reconstruct the vector-valued mild equation from its scalar coordinate
equations. The nonlinear Volterra uniqueness theorem then identifies any
two continuous mild solutions with the same initial datum, without a
small-time assumption. This permits compatible restarts of local solutions.
-/

open Set MeasureTheory
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {E V ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]
  [Fintype ι]

set_option maxHeartbeats 800000 in
/-- Reconstruct the full mild equation from the coordinate mild equations.
Only reconstruction of a vector from its coordinates is needed. -/
theorem IsFiniteHeatSystemMildOn.operator_mild
    {a : ι → ℝ} {P : ι → V →L[ℝ] ℝ} {f : V → V}
    (hf : ContDiff ℝ ∞ f) {T : ℝ} {u : ℝ → BUC E V}
    (hm : IsFiniteHeatSystemMildOn a P f hf.continuous T u)
    (Q : ι → ℝ →L[ℝ] V) (hPQ : ∀ z : V, ∑ i, Q i (P i z) = z)
    (hu : ContinuousOn u (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    u t = finiteHeatSystemOperator a P Q t (u 0) +
      ∫ r in 0..t, finiteHeatSystemOperator a P Q (t - r)
        (BUC.postcompContinuous f hf.continuous (u r)) := by
  have hrec (w : BUC E V) : ∑ i, BUC.postcompCLM (Q i) (BUC.postcompCLM (P i) w) = w := by
    apply BUC.ext
    intro y
    change (BUC.evalCLM (𝕜 := ℝ) y) (∑ i, _) = _
    rw [map_sum]
    exact hPQ (w y)
  let g (i : ι) (r : ℝ) := BUC.postcompContinuous (fun z ↦ P i (f z))
    ((P i).continuous.comp hf.continuous) (u r)
  have hgc (i : ι) : ContinuousOn (g i) (Icc 0 T) :=
    (BUC.continuous_postcompContinuous (fun z ↦ P i (f z))
      (((P i).contDiff.comp hf).of_le (by simp))).comp_continuousOn hu
  have hsrc (i : ι) (r : ℝ) :
      BUC.postcompCLM (P i) (BUC.postcompContinuous f hf.continuous (u r)) = g i r :=
    BUC.ext fun _ ↦ rfl
  have hci (i : ι) : IntervalIntegrable (fun r ↦ heatFlowBUC (a i) (t - r) (g i r))
      volume 0 t := by
    have hc : ContinuousOn (fun r ↦ heatFlowBUC (a i) (t - r) (g i r)) (Icc 0 T) :=
      (continuous_heatFlowBUC_joint (a i)).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk (hgc i))
    apply ContinuousOn.intervalIntegrable
    exact hc.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  have hcoord (i : ι) : BUC.postcompCLM (P i) (u t) =
      heatFlowBUC (a i) t (BUC.postcompCLM (P i) (u 0)) +
        ∫ r in 0..t, heatFlowBUC (a i) (t - r) (g i r) := by
    simpa only [zero_add, heatDuhamel, g] using hm 0 t le_rfl ht.1 (by simpa using ht.2) i
  rw [← hrec (u t)]
  simp_rw [hcoord, map_add,
    ← (BUC.postcompCLM (Q _)).intervalIntegral_comp_comm (hci _)]
  rw [Finset.sum_add_distrib, finiteHeatSystemOperator_apply]
  congr 1
  rw [show (fun r ↦ finiteHeatSystemOperator a P Q (t - r)
      (BUC.postcompContinuous f hf.continuous (u r))) =
      (fun r ↦ ∑ i, BUC.postcompCLM (Q i) (heatFlowBUC (a i) (t - r) (g i r))) by
    funext r
    simp only [finiteHeatSystemOperator_apply, hsrc]]
  exact (intervalIntegral.integral_finsetSum fun i _ ↦
    ⟨(BUC.postcompCLM (Q i)).integrable_comp (hci i).1,
      (BUC.postcompCLM (Q i)).integrable_comp (hci i).2⟩).symm

set_option maxHeartbeats 800000 in
/-- Continuous solutions of the same coupled finite heat system with the
same initial datum agree throughout their common finite time interval. -/
theorem IsFiniteHeatSystemMildOn.eqOn
    {a : ι → ℝ} {P : ι → V →L[ℝ] ℝ} {f : V → V}
    (hf : ContDiff ℝ ∞ f) {T : ℝ} (hT : 0 ≤ T) {u v : ℝ → BUC E V}
    (hmu : IsFiniteHeatSystemMildOn a P f hf.continuous T u)
    (hmv : IsFiniteHeatSystemMildOn a P f hf.continuous T v)
    (Q : ι → ℝ →L[ℝ] V) (hPQ : ∀ z : V, ∑ i, Q i (P i z) = z)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hinit : u 0 = v 0) : EqOn u v (Icc 0 T) := by
  apply eqOn_of_nonlinearVolterra_lipschitzOn_balls
    (finiteHeatSystemOperator a P Q) (continuous_finiteHeatSystemOperator_joint a P Q)
    (BUC.postcompContinuous f hf.continuous)
    (BUC.continuous_postcompContinuous f (hf.of_le (by simp)))
    (BUC.exists_postcompContinuous_lipschitz_bound f (hf.of_le (by simp)))
    hT (Finset.sum_nonneg fun i _ ↦ mul_nonneg (norm_nonneg (Q i)) (norm_nonneg (P i)))
    (fun t _ ↦ norm_finiteHeatSystemOperator_le a P Q t) hu hv
  · exact fun t ht ↦ hmu.operator_mild hf Q hPQ hu ht
  · intro t ht
    simpa only [hinit] using hmv.operator_mild hf Q hPQ hv ht

end

end Planarwave
