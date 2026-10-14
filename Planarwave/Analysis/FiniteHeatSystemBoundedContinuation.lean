/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.FiniteHeatSystemContinuation
public import Planarwave.Analysis.FiniteHeatSystemUniqueness

@[expose] public section

/-!
# Bounded-norm continuation for coupled heat systems

A solution on a finite half-open time interval, bounded in BUC, extends
strictly beyond its endpoint. Start a uniform-lifetime local solution
before the endpoint, glue it to the old solution, and use uniqueness to
identify the extension on the whole original interval. No convergence
of the old trajectory at the endpoint is presumed.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {E V ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]
  [Fintype ι]

omit [CompleteSpace V] [Fintype ι] in
/-- Restriction to a shorter time interval preserves all restart equations. -/
theorem IsFiniteHeatSystemMildOn.mono
    {a : ι → ℝ} {P : ι → V →L[ℝ] ℝ} {f : V → V} {hf : Continuous f}
    {S T : ℝ} {u : ℝ → BUC E V}
    (hm : IsFiniteHeatSystemMildOn a P f hf T u) (hST : S ≤ T) :
    IsFiniteHeatSystemMildOn a P f hf S u :=
  fun s t hs ht hst i ↦ hm s t hs ht (hst.trans hST) i

omit [CompleteSpace V] [Fintype ι] in
/-- The mild equation depends only on the trajectory on its time slab. -/
theorem IsFiniteHeatSystemMildOn.congr
    {a : ι → ℝ} {P : ι → V →L[ℝ] ℝ} {f : V → V} {hf : Continuous f}
    {T : ℝ} {u v : ℝ → BUC E V}
    (hm : IsFiniteHeatSystemMildOn a P f hf T u) (heq : EqOn u v (Icc 0 T)) :
    IsFiniteHeatSystemMildOn a P f hf T v := by
  intro s t hs ht hst i
  have hsT : s ≤ T := by linarith
  rw [← heq ⟨add_nonneg hs ht, hst⟩, ← heq ⟨hs, hsT⟩, hm s t hs ht hst i]
  congr 1
  apply heatDuhamel_congr _ ht
  intro r hr
  dsimp only
  rw [heq ⟨add_nonneg hs hr.1, by linarith [hr.2]⟩]

omit [CompleteSpace V] [Fintype ι] in
/-- A finite-slab continuous mild solution admits a globally continuous
representative, constant outside the slab, without changing its equation. -/
theorem IsFiniteHeatSystemMildOn.exists_continuous_extension
    {a : ι → ℝ} {P : ι → V →L[ℝ] ℝ} {f : V → V} {hf : Continuous f}
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → BUC E V}
    (hm : IsFiniteHeatSystemMildOn a P f hf T u) (hu : ContinuousOn u (Icc 0 T)) :
    ∃ v : ℝ → BUC E V, Continuous v ∧ EqOn u v (Icc 0 T) ∧
      IsFiniteHeatSystemMildOn a P f hf T v := by
  let v := fun t ↦ u (projIcc 0 T hT t)
  have hv : Continuous v :=
    (continuousOn_iff_continuous_domRestrict.mp hu).comp continuous_projIcc
  have heq : EqOn u v (Icc 0 T) := by
    intro t ht
    simp only [v, projIcc_of_mem hT ht]
  exact ⟨v, hv, heq, hm.congr heq⟩

set_option maxHeartbeats 1200000 in
/-- A BUC-bounded solution on `[0,T)` for finite `T` extends beyond `T`.
The argument uses uniform local existence, gluing, and uniqueness; it
does not assume an endpoint value or endpoint limit. -/
theorem exists_finiteHeatSystem_extension_of_bounded
    [DecidableEq ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V)
    (hPQ : ∀ z : V, ∑ i, Q i (P i z) = z)
    (hQP : ∀ i j z, P i (Q j z) = if i = j then z else 0)
    (f : V → V) (hf : ContDiff ℝ ∞ f)
    {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B) {u : ℝ → BUC E V}
    (hu : ContinuousOn u (Ico 0 T)) (hb : ∀ t ∈ Ico 0 T, ‖u t‖ ≤ B)
    (hm : ∀ S ∈ Ico 0 T, IsFiniteHeatSystemMildOn a P f hf.continuous S u) :
    ∃ S > T, ∃ w : ℝ → BUC E V, Continuous w ∧ EqOn u w (Ico 0 T) ∧
      IsFiniteHeatSystemMildOn a P f hf.continuous S w := by
  obtain ⟨τ, hτ, _, hex⟩ := exists_local_finiteHeatSystem (E := E) a ha P Q hPQ hQP f hf hB
  let s := max 0 (T - τ / 2)
  have hs : 0 ≤ s := le_max_left _ _
  have hsT : s < T := max_lt hT (by linarith)
  have hlong : T < s + τ := by
    have h := le_max_right 0 (T - τ / 2)
    dsimp [s]
    linarith
  have hus : ContinuousOn u (Icc 0 s) := hu.mono (fun _ ht ↦ ⟨ht.1, ht.2.trans_lt hsT⟩)
  obtain ⟨v, hv, hinit, _, hmv⟩ := hex (u s) (hb s ⟨hs, hsT⟩)
  let z := finiteHeatSystemSplice s u v
  have hz : ContinuousOn z (Icc 0 (s + τ)) :=
    continuousOn_finiteHeatSystemSplice hs hτ.le hus hv.continuousOn hinit
  have hmz : IsFiniteHeatSystemMildOn a P f hf.continuous (s + τ) z :=
    (hm s ⟨hs, hsT⟩).splice ha hf hs hτ.le hmv hus hv.continuousOn hinit
  obtain ⟨w, hw, hzw, hmw⟩ := hmz.exists_continuous_extension (add_nonneg hs hτ.le) hz
  refine ⟨s + τ, hlong, w, hw, ?_, hmw⟩
  have hinitw : u 0 = w 0 := by
    have hh := hzw ⟨le_rfl, add_nonneg hs hτ.le⟩
    simpa only [z, finiteHeatSystemSplice_zero u v hs] using hh
  intro t ht
  have htS : t ≤ s + τ := ht.2.le.trans hlong.le
  have hut : ContinuousOn u (Icc 0 t) := hu.mono (fun _ hr ↦ ⟨hr.1, hr.2.trans_lt ht.2⟩)
  exact (hm t ht).eqOn hf ht.1 (hmw.mono htS) Q hPQ hut hw.continuousOn hinitw
    ⟨ht.1, le_rfl⟩

end

end Planarwave
