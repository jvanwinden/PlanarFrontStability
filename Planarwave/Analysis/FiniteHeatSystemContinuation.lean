/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.FiniteHeatSystemUniqueness

@[expose] public section

/-!
# Gluing restarted finite heat-system solutions

Splice a solution on `[0,S]` with a new local solution whose initial datum
is the old terminal value. The join is continuous in BUC norm, and the
Duhamel restart identity proves that it is a mild solution on `[0,S+T]`.
This is the concrete extension step in bounded-norm continuation.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

section Splice

variable {X : Type*}

/-- Join an old path to a restarted path at time `S`. -/
def finiteHeatSystemSplice (S : ℝ) (u v : ℝ → X) (t : ℝ) : X :=
  if t ≤ S then u t else v (t - S)

theorem finiteHeatSystemSplice_of_le {S t : ℝ} (u v : ℝ → X) (ht : t ≤ S) :
    finiteHeatSystemSplice S u v t = u t := if_pos ht

theorem finiteHeatSystemSplice_of_ge {S t : ℝ} {u v : ℝ → X}
    (hinit : v 0 = u S) (ht : S ≤ t) :
    finiteHeatSystemSplice S u v t = v (t - S) := by
  by_cases h : t ≤ S
  · have heq : t = S := le_antisymm h ht
    simp only [heq, finiteHeatSystemSplice, le_refl, ite_true, sub_self, hinit]
  · exact if_neg h

theorem finiteHeatSystemSplice_zero {S : ℝ} (u v : ℝ → X) (hS : 0 ≤ S) :
    finiteHeatSystemSplice S u v 0 = u 0 := finiteHeatSystemSplice_of_le u v hS

/-- Continuity at the splice follows from the matching endpoint values. -/
theorem continuousOn_finiteHeatSystemSplice [TopologicalSpace X]
    {S T : ℝ} (_hS : 0 ≤ S) (_hT : 0 ≤ T) {u v : ℝ → X}
    (hu : ContinuousOn u (Icc 0 S)) (hv : ContinuousOn v (Icc 0 T))
    (hinit : v 0 = u S) : ContinuousOn (finiteHeatSystemSplice S u v) (Icc 0 (S + T)) := by
  have hl : ContinuousOn (finiteHeatSystemSplice S u v) (Icc 0 S) :=
    hu.congr fun t ht ↦ finiteHeatSystemSplice_of_le u v ht.2
  have hvc : ContinuousOn (fun t ↦ v (t - S)) (Icc S (S + T)) :=
    hv.comp (continuousOn_id.sub continuousOn_const) (fun t ht ↦ by
      constructor <;> linarith [ht.1, ht.2])
  have hr : ContinuousOn (finiteHeatSystemSplice S u v) (Icc S (S + T)) :=
    hvc.congr fun t ht ↦ finiteHeatSystemSplice_of_ge hinit ht.1
  apply (hl.union_of_isClosed hr isClosed_Icc isClosed_Icc).mono
  intro t ht
  by_cases h : t ≤ S
  · exact Or.inl ⟨ht.1, h⟩
  · exact Or.inr ⟨(lt_of_not_ge h).le, ht.2⟩

end Splice

variable {E V ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]
  [Fintype ι]

set_option maxHeartbeats 1200000 in
/-- A compatible restarted local solution extends a mild solution. The
coordinate Duhamel equation across the join follows from heat evolution
and the translated-source restart formula. -/
theorem IsFiniteHeatSystemMildOn.splice
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {P : ι → V →L[ℝ] ℝ}
    {f : V → V} (hf : ContDiff ℝ ∞ f)
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) {u v : ℝ → BUC E V}
    (hmu : IsFiniteHeatSystemMildOn a P f hf.continuous S u)
    (hmv : IsFiniteHeatSystemMildOn a P f hf.continuous T v)
    (hu : ContinuousOn u (Icc 0 S)) (hv : ContinuousOn v (Icc 0 T))
    (hinit : v 0 = u S) :
    IsFiniteHeatSystemMildOn a P f hf.continuous (S + T) (finiteHeatSystemSplice S u v) := by
  let w := finiteHeatSystemSplice S u v
  have hw : ContinuousOn w (Icc 0 (S + T)) :=
    continuousOn_finiteHeatSystemSplice hS hT hu hv hinit
  have hw₀ : w 0 = u 0 := finiteHeatSystemSplice_zero u v hS
  let F (i : ι) : BUC E V → BUC E ℝ := BUC.postcompContinuous (fun z ↦ P i (f z))
    ((P i).continuous.comp hf.continuous)
  have hFc (i : ι) : Continuous (F i) :=
    BUC.continuous_postcompContinuous (fun z ↦ P i (f z))
      (((P i).contDiff.comp hf).of_le (by simp))
  have hu₀ (t : ℝ) (ht : t ∈ Icc 0 S) (i : ι) :
      BUC.postcompCLM (P i) (u t) =
        heatFlowBUC (a i) t (BUC.postcompCLM (P i) (u 0)) +
          heatDuhamel (a i) (fun r ↦ F i (u r)) t := by
    simpa only [zero_add, F] using hmu 0 t le_rfl ht.1 (by simpa using ht.2) i
  have hv₀ (t : ℝ) (ht : t ∈ Icc 0 T) (i : ι) :
      BUC.postcompCLM (P i) (v t) =
        heatFlowBUC (a i) t (BUC.postcompCLM (P i) (v 0)) +
          heatDuhamel (a i) (fun r ↦ F i (v r)) t := by
    simpa only [zero_add, F] using hmv 0 t le_rfl ht.1 (by simpa using ht.2) i
  apply isFiniteHeatSystemMildOn_of_mild a ha P f hf hw
  intro t ht i
  change BUC.postcompCLM (P i) (w t) =
    heatFlowBUC (a i) t (BUC.postcompCLM (P i) (w 0)) +
      heatDuhamel (a i) (fun r ↦ F i (w r)) t
  rw [hw₀]
  by_cases hts : t ≤ S
  · rw [show w t = u t from finiteHeatSystemSplice_of_le u v hts, hu₀ t ⟨ht.1, hts⟩ i]
    congr 1
    apply heatDuhamel_congr (a i) ht.1
    intro r hr
    dsimp only
    rw [show w r = u r from finiteHeatSystemSplice_of_le u v (hr.2.trans hts)]
  · have hst : S ≤ t := (lt_of_not_ge hts).le
    have hage : 0 ≤ t - S := sub_nonneg.mpr hst
    have hageT : t - S ≤ T := by linarith [ht.2]
    have hsource : ContinuousOn (fun r ↦ F i (w r)) (Icc 0 (S + (t - S))) := by
      apply (hFc i).comp_continuousOn
      exact hw.mono (Icc_subset_Icc le_rfl (by linarith [ht.2]))
    have hleft : heatDuhamel (a i) (fun r ↦ F i (w r)) S =
        heatDuhamel (a i) (fun r ↦ F i (u r)) S := by
      apply heatDuhamel_congr (a i) hS
      intro r hr
      dsimp only
      rw [show w r = u r from finiteHeatSystemSplice_of_le u v hr.2]
    have hright : heatDuhamel (a i) (fun r ↦ F i (w (S + r))) (t - S) =
        heatDuhamel (a i) (fun r ↦ F i (v r)) (t - S) := by
      apply heatDuhamel_congr (a i) hage
      intro r hr
      dsimp only
      have heq : w (S + r) = v r := by
        simpa only [add_sub_cancel_left] using
          finiteHeatSystemSplice_of_ge hinit (show S ≤ S + r by linarith [hr.1])
      rw [heq]
    have hd : heatDuhamel (a i) (fun r ↦ F i (w r)) t =
        heatFlowBUC (a i) (t - S) (heatDuhamel (a i) (fun r ↦ F i (u r)) S) +
          heatDuhamel (a i) (fun r ↦ F i (v r)) (t - S) := by
      have h := heatDuhamel_restart_shift (ha i) hS hage hsource
      rw [hleft, hright] at h
      simpa only [add_sub_cancel] using h
    rw [show w t = v (t - S) from finiteHeatSystemSplice_of_ge hinit hst,
      hv₀ (t - S) ⟨hage, hageT⟩ i, hinit, hu₀ S ⟨hS, le_rfl⟩ i,
      heatFlowBUC_add, ← heatFlowBUC_add_apply (ha i) hage hS, hd]
    rw [sub_add_cancel]
    exact add_assoc _ _ _

end

end Planarwave
