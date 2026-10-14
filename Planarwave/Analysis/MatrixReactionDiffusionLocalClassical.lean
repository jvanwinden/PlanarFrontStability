/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionSpacetime
import Planarwave.Analysis.FiniteHeatSystemBoundedContinuation

/-!
# Classical regularity from finite-slab continuity

A maximal trajectory need only be continuous on its actual interval of
existence. On each compact time slab, extend the trajectory constantly
past the endpoints, obtain a norm bound by compactness, and apply the
already proved classical regularity of continuous mild solutions.
Local agreement transfers the result back to the original trajectory.
-/

open Filter Set
open scoped ContDiff Laplacian Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- A mild solution continuous only on its finite time slab is jointly
smooth at positive interior times. No additional norm bound is needed. -/
theorem IsMatrixReactionDiffusionMildOn.contDiffOn_infty_of_continuousOn
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T : ℝ} {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ u p.1 p.2) (Ioo 0 T ×ˢ univ) := by
  obtain ⟨v, hv, heq, hmv⟩ :=
    IsFiniteHeatSystemMildOn.exists_continuous_extension hT hm hu
  have hmv' : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T v := hmv
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.continuousOn : ContinuousOn v (Icc 0 T))
  have hbound : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ max R 0 :=
    fun t ht ↦ (hR t ht).trans (le_max_left _ _)
  apply (hmv'.contDiffOn_infty h₁ hv (le_max_right _ _) hbound).congr
  intro p hp
  exact congrArg (fun w : BUC E (ℝ^n) ↦ w p.2) (heq ⟨hp.1.1.le, hp.1.2.le⟩)

/-- A mild solution continuous only on its finite time slab satisfies
the actual matrix reaction--diffusion PDE at positive interior times. -/
theorem IsMatrixReactionDiffusionMildOn.hasDerivAt_of_continuousOn
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T : ℝ} {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : E) :
    HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → ℝ^n) x) + f (u t x)) t := by
  obtain ⟨v, hv, heq, hmv⟩ :=
    IsFiniteHeatSystemMildOn.exists_continuous_extension hT hm hu
  have hmv' : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T v := hmv
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.continuousOn : ContinuousOn v (Icc 0 T))
  have hbound : ∀ r ∈ Icc 0 T, ‖v r‖ ≤ max R 0 :=
    fun r hr ↦ (hR r hr).trans (le_max_left _ _)
  have htime := hmv'.hasDerivAt h₁ hv (le_max_right _ _) hbound ht x
  rw [← heq ⟨ht.1.le, ht.2.le⟩] at htime
  apply htime.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact congrArg (fun w : BUC E (ℝ^n) ↦ w x) (heq ⟨hr.1.le, hr.2.le⟩)

end

end Planarwave
