/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionSpacetime
import Planarwave.Analysis.FiniteHeatSystemBoundedContinuation

/-!
# Bounded-norm continuation for the original matrix equation

A BUC-bounded mild solution on a finite half-open time interval extends
to a larger interval. The extension is a genuine classical solution,
jointly smooth at positive times and satisfying the original PDE, with
the challenge's exact BUC condition on its finite time slab.
-/

open Set
open scoped ContDiff InnerProductSpace Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- A finite half-open interval with a bounded BUC solution cannot be
maximal. The extended solution agrees on the entire original interval. -/
theorem exists_matrixReactionDiffusion_extension_of_bounded
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B) {u : ℝ → BUC E (ℝ^n)}
    (hu : ContinuousOn u (Ico 0 T)) (hb : ∀ t ∈ Ico 0 T, ‖u t‖ ≤ B)
    (hm : ∀ S ∈ Ico 0 T,
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive S u) :
    ∃ S > T, ∃ w : ℝ → BUC E (ℝ^n), Continuous w ∧ EqOn u w (Ico 0 T) ∧
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive S w ∧
      IsBUCOn (fun p : ℝ × E ↦ w p.1 p.2) (Icc 0 S ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ w p.1 p.2) (Ioo 0 S ×ˢ univ) ∧
      ∀ t ∈ Ioo 0 S, ∀ x,
        HasDerivAt (fun r ↦ w r x) (D (Δ (w t : E → ℝ^n) x) + f (w t x)) t := by
  let b := h₁.positive.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let P := matrixDiffusionCoordinate D h₁.positive
  let Q (i : Fin n) := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hPQ (z : ℝ^n) : ∑ i, Q i (P i z) = z := b.sum_repr' z
  have hQP (i j : Fin n) (z : ℝ) : P i (Q j z) = if i = j then z else 0 := by
    change ⟪b i, z • b j⟫_ℝ = _
    rw [real_inner_smul_right, b.inner_eq_ite]
    split_ifs <;> simp
  obtain ⟨S, hS, w, hw, heq, hmw⟩ := exists_finiteHeatSystem_extension_of_bounded
    (diffusionEigenvalues D h₁.positive) (diffusionEigenvalues_nonneg D h₁.positive)
    P Q hPQ hQP f h₁.smooth hT hB hu hb hm
  have hmw' : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive S w := hmw
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.continuousOn : ContinuousOn w (Icc 0 S))
  have hbound : ∀ t ∈ Icc 0 S, ‖w t‖ ≤ max R 0 :=
    fun t ht ↦ (hR t ht).trans (le_max_left _ _)
  exact ⟨S, hS, w, hw, heq, hmw', isBUCOn_buc_trajectory_slab hw.continuousOn,
    hmw'.contDiffOn_infty h₁ hw (le_max_right _ _) hbound,
    fun _ ht x ↦ hmw'.hasDerivAt h₁ hw (le_max_right _ _) hbound ht x⟩

end

end Planarwave
