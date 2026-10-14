/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialRegularityLocal

@[expose] public section

/-!
# Relative locality of time-continuous BUC spatial jets

Spatial derivatives are unique, so local BUC jets also glue on relative
time neighborhoods. In particular this keeps the right endpoint of a finite
existence interval; no continuation beyond that endpoint is required.
-/

open Set Filter
open scoped Topology

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Spatial BUC jets glue over neighborhoods relative to the time domain.
The explicit membership hypothesis also covers isolated times. -/
theorem BUCSpatialRegularOn.of_locallyWithin {s : Set ℝ} {k : ℕ}
    {f : ℝ → BUC E F}
    (hlocal : ∀ t ∈ s, ∃ r : Set ℝ,
      r ⊆ s ∧ t ∈ r ∧ r ∈ 𝓝[s] t ∧ BUCSpatialRegularOn r k f) :
    BUCSpatialRegularOn s k f := by
  classical
  induction k generalizing F with
  | zero =>
    intro t ht
    obtain ⟨r, _, htr, hr, hf⟩ := hlocal t ht
    exact (hf.continuous t htr).mono_of_mem_nhdsWithin hr
  | succ k ih =>
    have hc : ContinuousOn f s := by
      intro t ht
      obtain ⟨r, _, htr, hr, hf⟩ := hlocal t ht
      exact (hf.continuous t htr).mono_of_mem_nhdsWithin hr
    have hex : ∀ t ∈ s, ∃ q : BUC E (E →L[ℝ] F),
        ∀ x, HasFDerivAt (f t) (q x) x := by
      intro t ht
      obtain ⟨r, _, htr, _, _, q, _, hd⟩ := hlocal t ht
      exact ⟨q t, hd t htr⟩
    let q : ℝ → BUC E (E →L[ℝ] F) := fun t ↦
      if ht : t ∈ s then (hex t ht).choose else 0
    have hq : ∀ t ∈ s, ∀ x, HasFDerivAt (f t) (q t x) x := by
      intro t ht
      simpa only [q, dif_pos ht] using (hex t ht).choose_spec
    refine ⟨hc, q, ih ?_, hq⟩
    intro t ht
    obtain ⟨r, hrs, htr, hr, _, p, hp, hd⟩ := hlocal t ht
    refine ⟨r, hrs, htr, hr, hp.congr ?_⟩
    intro v hv
    exact BUC.ext fun x ↦ (hd v hv x).unique (hq v (hrs hv) x)

end

end Planarwave
