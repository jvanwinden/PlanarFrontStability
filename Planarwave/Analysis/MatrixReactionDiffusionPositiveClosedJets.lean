/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionRegularity
import Planarwave.Analysis.BUCSpatialRegularityWithin

/-!
# Positive-time BUC jets up to a finite right endpoint

Compactness bounds a continuous mild trajectory on its finite slab. Parabolic
smoothing supplies genuine spatial jets on every smaller positive-time closed
slab, and relative locality glues them while retaining the right endpoint.
-/

open Set Filter
open scoped Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- All spatial BUC jets of a continuous finite-slab mild solution are
continuous at every positive time, including the right endpoint relative
to the slab. No additional bound on the physical trajectory is assumed. -/
theorem IsMatrixReactionDiffusionMildOn.spatialRegularOn_Ioc
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hu : ContinuousOn u (Icc 0 T)) (k : ℕ) :
    BUCSpatialRegularOn (Ioc 0 T) k u := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  have hB₀ : 0 ≤ B := (norm_nonneg (u 0)).trans (hB 0 ⟨le_rfl, hT⟩)
  apply BUCSpatialRegularOn.of_locallyWithin
  intro t ht
  have hδ : 0 < t / 2 := div_pos ht.1 (by norm_num)
  have hδt : t / 2 < t := by linarith [ht.1]
  obtain ⟨C, hC, hreg⟩ := exists_matrixReactionDiffusion_cn_bound
    (E := E) f D h₁ k hδ hB₀
  refine ⟨Icc (t / 2) T, ?_, ⟨hδt.le, ht.2⟩, ?_, (hreg T hT u hu hB hm).1⟩
  · intro r hr
    exact ⟨hδ.trans_le hr.1, hr.2⟩
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hδt),
      self_mem_nhdsWithin] with r hr hrt
    exact ⟨hr.le, hrt.2⟩

end

end Planarwave
