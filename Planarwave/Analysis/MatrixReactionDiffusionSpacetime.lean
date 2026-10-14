/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionLocalExistence
import Planarwave.Analysis.ReactionDiffusionSpacetime
import Planarwave.Analysis.ReactionDiffusionSmooth

/-!
# Spacetime regularity of the constructed matrix solutions

Norm continuity at time zero gives exactly the challenge's `IsBUCOn`
condition on a finite time slab. The positive-time spatial estimates and
the actual PDE give joint `C∞` regularity, including all mixed derivatives.
Continuation remains a separate obligation.
-/

open Set
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

/-- The challenge's finite-slab continuity predicate follows from BUC
norm continuity, without assumptions on initial spatial derivatives. -/
theorem isBUCOn_buc_trajectory_slab {E F : Type*} [PseudoMetricSpace E]
    [NormedAddCommGroup F] {u : ℝ → BUC E F} {T : ℝ}
    (hu : ContinuousOn u (Icc 0 T)) :
    IsBUCOn (fun p : ℝ × E ↦ u p.1 p.2) (Icc 0 T ×ˢ univ) :=
  ⟨BUC.uniformContinuousOn_uncurry isCompact_Icc hu,
    BUC.exists_bound_uncurry isCompact_Icc hu⟩

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- Joint positive-time differentiability of any bounded matrix mild
solution, derived from its parabolic spatial regularity and pointwise PDE. -/
theorem IsMatrixReactionDiffusionMildOn.contDiffOn_one
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T B : ℝ} {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) :
    ContDiffOn ℝ 1 (fun p : ℝ × E ↦ u p.1 p.2) (Ioo 0 T ×ˢ univ) := by
  intro p hp
  have hhalf : 0 < p.1 / 2 := div_pos hp.1.1 (by norm_num)
  obtain ⟨C, _, hCb⟩ := exists_matrixReactionDiffusion_cn_bound (E := E) f D h₁ 2 hhalf hB
  have hreg := (hCb T (hp.1.1.trans hp.1.2).le u hu.continuousOn hb hm).1
  have hopen : IsOpen (Ioo (p.1 / 2) T ×ˢ (univ : Set E)) := isOpen_Ioo.prod isOpen_univ
  have hc : ContDiffOn ℝ 1 (fun z : ℝ × E ↦ u z.1 z.2)
      (Ioo (p.1 / 2) T ×ˢ univ) :=
    (hreg.mono Ioo_subset_Icc_self).contDiffOn_one_reactionDiffusion isOpen_Ioo D f
      (h₁.smooth.of_le (by simp)) (fun t ht x ↦
        hm.hasDerivAt h₁ hu hB hb ⟨hhalf.trans ht.1, ht.2⟩ x)
  exact (hc.contDiffAt (hopen.mem_nhds ⟨⟨by linarith [hp.1.1], hp.1.2⟩, mem_univ _⟩)).contDiffWithinAt

/-- The same constructed matrix solution is jointly `C²`, including
the second time derivative and the mixed time--space derivatives. -/
theorem IsMatrixReactionDiffusionMildOn.contDiffOn_two
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T B : ℝ} {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) :
    ContDiffOn ℝ 2 (fun p : ℝ × E ↦ u p.1 p.2) (Ioo 0 T ×ˢ univ) := by
  intro p hp
  have hhalf : 0 < p.1 / 2 := div_pos hp.1.1 (by norm_num)
  obtain ⟨C, _, hCb⟩ := exists_matrixReactionDiffusion_cn_bound (E := E) f D h₁ 4 hhalf hB
  have hreg := (hCb T (hp.1.1.trans hp.1.2).le u hu.continuousOn hb hm).1
  have hopen : IsOpen (Ioo (p.1 / 2) T ×ˢ (univ : Set E)) := isOpen_Ioo.prod isOpen_univ
  have hc := hreg.contDiffOn_two_reactionDiffusion D f h₁.smooth (fun t ht x ↦
    hm.hasDerivAt h₁ hu hB hb ⟨hhalf.trans ht.1, ht.2⟩ x)
  exact (hc.contDiffAt (hopen.mem_nhds ⟨⟨by linarith [hp.1.1], hp.1.2⟩, mem_univ _⟩)).contDiffWithinAt

/-- Every bounded matrix mild solution is jointly smooth at positive
interior times. The all-order induction includes the time derivatives. -/
theorem IsMatrixReactionDiffusionMildOn.contDiffOn_infty
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T B : ℝ} {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ u p.1 p.2) (Ioo 0 T ×ˢ univ) := by
  intro p hp
  have hhalf : 0 < p.1 / 2 := div_pos hp.1.1 (by norm_num)
  have hreg : ∀ j, BUCSpatialRegularOn (Icc (p.1 / 2) T) j u := by
    intro j
    obtain ⟨C, _, hCb⟩ := exists_matrixReactionDiffusion_cn_bound (E := E) f D h₁ j hhalf hB
    exact (hCb T (hp.1.1.trans hp.1.2).le u hu.continuousOn hb hm).1
  have hopen : IsOpen (Ioo (p.1 / 2) T ×ˢ (univ : Set E)) := isOpen_Ioo.prod isOpen_univ
  have hc := BUCSpatialRegularOn.contDiffOn_infty_reactionDiffusion hreg D f h₁.smooth
    (fun t ht x ↦ hm.hasDerivAt h₁ hu hB hb ⟨hhalf.trans ht.1, ht.2⟩ x)
  exact (hc.contDiffAt (hopen.mem_nhds ⟨⟨by linarith [hp.1.1], hp.1.2⟩, mem_univ _⟩)).contDiffWithinAt

/-- Local matrix solutions attain their BUC initial data, satisfy the
exact slab continuity condition and pointwise PDE, and are jointly `C∞`
at positive times. The lifetime is uniform on bounded initial-data sets. -/
theorem exists_local_matrixReactionDiffusion_spacetime
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ T > 0, T ≤ 1 ∧ ∃ R > 0, ∀ u₀ : BUC E (ℝ^n), ‖u₀‖ ≤ B →
      ∃ u : ℝ → BUC E (ℝ^n), Continuous u ∧ u 0 = u₀ ∧ (∀ t, ‖u t‖ ≤ R) ∧
        IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u ∧
        IsBUCOn (fun p : ℝ × E ↦ u p.1 p.2) (Icc 0 T ×ˢ univ) ∧
        ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ u p.1 p.2) (Ioo 0 T ×ˢ univ) ∧
        ∀ t ∈ Ioo 0 T, ContDiff ℝ ∞ (u t : E → ℝ^n) ∧
          ∀ x, HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → ℝ^n) x) + f (u t x)) t := by
  obtain ⟨T, hT, hT₁, R, hR, hex⟩ := exists_local_matrixReactionDiffusion_pde (E := E) f D h₁ hB
  refine ⟨T, hT, hT₁, R, hR, fun u₀ hu₀ ↦ ?_⟩
  obtain ⟨u, hu, hinit, hb, hm, hpde⟩ := hex u₀ hu₀
  exact ⟨u, hu, hinit, hb, hm, isBUCOn_buc_trajectory_slab hu.continuousOn,
    hm.contDiffOn_infty h₁ hu hR.le (fun t _ ↦ hb t), hpde⟩

end

end Planarwave
