/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialBounds

@[expose] public section

/-!
# Locality of time-continuous spatial jets

Uniqueness of spatial derivatives glues locally constructed BUC jets.
This lets positive-time parabolic smoothing on compact slabs supply jets
on the whole open time interval, without regularity of the initial datum.
-/

open Set Filter
open scoped Topology

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BUCSpatialBound.regularOn_const {k : ℕ} {f : BUC E F} {A : ℝ}
    (hf : BUCSpatialBound k f A) (s : Set ℝ) :
    BUCSpatialRegularOn s k (fun _ ↦ f) := by
  induction k generalizing F with
  | zero => exact continuousOn_const
  | succ k ih =>
    obtain ⟨_, q, hq, hd⟩ := hf
    exact ⟨continuousOn_const, fun _ ↦ q, ih hq, fun _ _ x ↦ hd x⟩

/-- Spatial regularity is local in time. The neighborhoods may depend on
the time and the order of differentiability. -/
theorem BUCSpatialRegularOn.of_locally {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hlocal : ∀ t ∈ s, ∃ r : Set ℝ, r ⊆ s ∧ r ∈ 𝓝 t ∧ BUCSpatialRegularOn r k f) :
    BUCSpatialRegularOn s k f := by
  classical
  induction k generalizing F with
  | zero =>
    intro t ht
    obtain ⟨r, hrs, hr, hf⟩ := hlocal t ht
    exact (hf.continuous.continuousAt hr).continuousWithinAt
  | succ k ih =>
    have hc : ContinuousOn f s := by
      intro t ht
      obtain ⟨r, hrs, hr, hf⟩ := hlocal t ht
      exact (hf.continuous.continuousAt hr).continuousWithinAt
    have hex : ∀ t ∈ s, ∃ q : BUC E (E →L[ℝ] F), ∀ x, HasFDerivAt (f t) (q x) x := by
      intro t ht
      obtain ⟨r, hrs, hr, hfc, q, hq, hd⟩ := hlocal t ht
      exact ⟨q t, hd t (mem_of_mem_nhds hr)⟩
    let q : ℝ → BUC E (E →L[ℝ] F) := fun t ↦
      if ht : t ∈ s then (hex t ht).choose else 0
    have hq : ∀ t ∈ s, ∀ x, HasFDerivAt (f t) (q t x) x := by
      intro t ht
      simpa only [q, dif_pos ht] using (hex t ht).choose_spec
    refine ⟨hc, q, ih ?_, hq⟩
    intro t ht
    obtain ⟨r, hrs, hr, hfc, p, hp, hd⟩ := hlocal t ht
    refine ⟨r, hrs, hr, hp.congr ?_⟩
    intro v hv
    exact BUC.ext fun x ↦ (hd v hv x).unique (hq v (hrs hv) x)

end

end Planarwave
