/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionRegularity
import Planarwave.Analysis.FiniteHeatSystemUniqueness

/-!
# Uniqueness of the original matrix reaction--diffusion mild solutions

The real diffusion eigenbasis reconstructs the vector-valued state, so
finite-system uniqueness applies to the original matrix and smooth reaction.
On a compact time interval, continuity in BUC already supplies the norm
bound needed by the local Lipschitz estimate. No spatial regularity or
smallness of the interval or initial datum is assumed.
-/

open Set
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

/-- Uniqueness of continuous BUC mild solutions under the challenge's
original smooth parabolic hypotheses, on every common compact interval. -/
theorem IsMatrixReactionDiffusionMildOn.eqOn
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T : ℝ} (hT : 0 ≤ T) {u v : ℝ → BUC E (ℝ^n)}
    (hmu : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hmv : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T v)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hinit : u 0 = v 0) : EqOn u v (Icc 0 T) := by
  let b := h₁.positive.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let Q (i : Fin n) := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hPQ (z : ℝ^n) : ∑ i, Q i (matrixDiffusionCoordinate D h₁.positive i z) = z :=
    b.sum_repr' z
  exact IsFiniteHeatSystemMildOn.eqOn h₁.smooth hT hmu hmv Q hPQ hu hv hinit

end

end Planarwave
