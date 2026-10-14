/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-!
# Joint continuity of BUC trajectories

Evaluation is jointly continuous, and a compact family of BUC functions
has a common spatial modulus of continuity. Consequently a norm-continuous
BUC trajectory is bounded uniformly continuous on each compact time slab,
including the initial time. No spatial differentiability is required.
-/

open Set Metric

namespace BUC

section Metric

variable {A F : Type*} [PseudoMetricSpace A] [PseudoMetricSpace F]

/-- Joint evaluation, not just evaluation at one fixed spatial point. -/
theorem continuous_eval_joint : Continuous (fun p : BUC A F × A ↦ p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith _ 1
    (fun f ↦ f.continuous) lipschitz_eval

/-- BUC norm continuity in time implies joint pointwise continuity. -/
theorem continuousOn_uncurry {s : Set ℝ} {u : ℝ → BUC A F} (hu : ContinuousOn u s) :
    ContinuousOn (fun p : ℝ × A ↦ u p.1 p.2) (s ×ˢ univ) := by
  exact continuous_eval_joint.comp_continuousOn
    ((hu.comp continuousOn_fst (fun _ hp ↦ hp.1)).prodMk continuousOn_snd)

/-- Compact families of BUC fields have a common spatial modulus. -/
theorem equiuniformContinuous_of_isCompact {K : Set (BUC A F)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f ∈ K, ∀ x y : A, dist x y < δ → dist (f x) (f y) < ε := by
  classical
  obtain ⟨S, _, hS, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 3 by positivity)
  have hfinite (I : Finset (BUC A F)) :
      ∃ δ > 0, ∀ f ∈ I, ∀ x y : A, dist x y < δ → dist (f x) (f y) < ε / 3 := by
    induction I using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun _ hf ↦ False.elim (Finset.notMem_empty _ hf)⟩
    | @insert f I hf ih =>
      obtain ⟨δ, hδ, hb⟩ := ih
      obtain ⟨η, hη, hfb⟩ := Metric.uniformContinuous_iff.mp f.uniformContinuous
        (ε / 3) (by positivity)
      refine ⟨min δ η, lt_min hδ hη, fun g hg x y hxy ↦ ?_⟩
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hfb (hxy.trans_le (min_le_right _ _))
      · exact hb g hg x y (hxy.trans_le (min_le_left _ _))
  obtain ⟨δ, hδ, hb⟩ := hfinite hS.toFinset
  refine ⟨δ, hδ, fun f hf x y hxy ↦ ?_⟩
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  have hfg' : dist f g < ε / 3 := hfg
  have hxy' := hb g (hS.mem_toFinset.mpr hg) x y hxy
  have hx := (dist_apply_le f g x).trans_lt hfg'
  have hy := (dist_apply_le g f y).trans_lt (by simpa [dist_comm] using hfg')
  calc
    dist (f x) (f y) ≤ dist (f x) (g x) + (dist (g x) (g y) + dist (g y) (f y)) :=
      (dist_triangle (f x) (g x) (f y)).trans
        (add_le_add le_rfl (dist_triangle (g x) (g y) (f y)))
    _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add hx (add_lt_add hxy' hy)
    _ = ε := by ring

/-- Norm-continuous trajectories are uniformly continuous jointly in
time and space on compact time intervals, despite the unbounded spatial domain. -/
theorem uniformContinuousOn_uncurry {s : Set ℝ} (hs : IsCompact s)
    {u : ℝ → BUC A F} (hu : ContinuousOn u s) :
    UniformContinuousOn (fun p : ℝ × A ↦ u p.1 p.2) (s ×ˢ univ) := by
  have ht := hs.uniformContinuousOn_of_continuous hu
  have hK : IsCompact (u '' s) := hs.image_of_continuousOn hu
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δt, hδt, hmodt⟩ := Metric.uniformContinuousOn_iff.mp ht (ε / 2) (by positivity)
  obtain ⟨δx, hδx, hmodx⟩ := equiuniformContinuous_of_isCompact hK
    (show 0 < ε / 2 by positivity)
  refine ⟨min δt δx, lt_min hδt hδx, fun p hp q hq hpq ↦ ?_⟩
  have htime : dist p.1 q.1 < δt := (le_max_left _ _).trans_lt
    (hpq.trans_le (min_le_left _ _))
  have hspace : dist p.2 q.2 < δx := (le_max_right _ _).trans_lt
    (hpq.trans_le (min_le_right _ _))
  calc
    dist (u p.1 p.2) (u q.1 q.2) ≤
        dist (u p.1 p.2) (u q.1 p.2) + dist (u q.1 p.2) (u q.1 q.2) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      ((dist_apply_le _ _ _).trans_lt (hmodt _ hp.1 _ hq.1 htime))
      (hmodx _ ⟨q.1, hq.1, rfl⟩ _ _ hspace)
    _ = ε := by ring

end Metric

section Norm

variable {A F : Type*} [PseudoMetricSpace A] [NormedAddCommGroup F]

/-- A continuous BUC trajectory has a common pointwise bound on a
compact time slab. This bound does not require compactness in space. -/
theorem exists_bound_uncurry {s : Set ℝ} (hs : IsCompact s)
    {u : ℝ → BUC A F} (hu : ContinuousOn u s) :
    ∃ C : ℝ, ∀ p ∈ s ×ˢ (univ : Set A), ‖u p.1 p.2‖ ≤ C := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hu
  exact ⟨C, fun p hp ↦ ((u p.1).norm_apply_le p.2).trans (hC _ hp.1)⟩

end Norm

end BUC
