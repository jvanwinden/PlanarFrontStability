/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionRegularity
import Planarwave.Analysis.BUCSpatialRegularityLocal

/-!
# Positive-time BUC jets for matrix reaction--diffusion solutions

Every finite-interval continuous mild solution has all spatial BUC jets
on the open positive-time interval. Compactness supplies the norm bound
needed by parabolic smoothing, and uniqueness of genuine derivatives
glues the regularity proved on smaller positive-time slabs.
-/

open Set
open scoped Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- All spatial derivative fields of a finite-interval mild solution are
continuous in the BUC norm at every positive interior time. No separate
uniform bound on the trajectory needs to be assumed. -/
theorem IsMatrixReactionDiffusionMildOn.spatialRegularOn_Ioo
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hu : ContinuousOn u (Icc 0 T)) (k : ℕ) :
    BUCSpatialRegularOn (Ioo 0 T) k u := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hB₀ : 0 ≤ B := (norm_nonneg (u 0)).trans (hB 0 ⟨le_rfl, hT⟩)
  apply BUCSpatialRegularOn.of_locally
  intro t ht
  have hδ : 0 < t / 2 := div_pos ht.1 (by norm_num)
  have hδt : t / 2 < t := by linarith [ht.1]
  obtain ⟨C, hC, hreg⟩ := exists_matrixReactionDiffusion_cn_bound
    (E := E) f D h₁ k hδ hB₀
  refine ⟨Ioo (t / 2) T, ?_, Ioo_mem_nhds hδt ht.2, ?_⟩
  · intro r hr
    exact ⟨hδ.trans hr.1, hr.2⟩
  · exact ((hreg T hT u hu hB hm).1).mono Ioo_subset_Icc_self

end

end Planarwave
