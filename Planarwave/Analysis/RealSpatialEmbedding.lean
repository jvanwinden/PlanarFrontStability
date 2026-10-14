/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAdjointEquation
import all Planarwave.Analysis.PhaseFunctional
import all Planarwave.Coordinates
import all Planarwave.Analysis.SpatialHeatFourier

/-!
# Real split-coordinate data in the complex spatial semigroup

The nonlinear equations use real data in `(y,z)` coordinates. The linear
semigroup estimates use complex data in full Euclidean coordinates. This
bounded linear map preserves the supremum norm exactly.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {d n : ℕ}

/-- Embed real split-coordinate spatial data into the semigroup's space. -/
def embedSplitSpatial (hd : 2 ≤ d) :
    BUC (ℝ^(d - 1) × ℝ) (ℝ^n) →L[ℝ] BUC (ℝ^d) (ℂ^n) :=
  (BUC.postcompCLM realStateEmbeddingCLM).comp
    (BUC.compCLM (𝕜 := ℝ) (coordinateEquiv hd) (coordinateEquiv hd).toContinuousLinearMap.uniformContinuous)

@[simp]
theorem embedSplitSpatial_apply (hd : 2 ≤ d) (v : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) (x : ℝ^d) :
    embedSplitSpatial hd v x = embed (v (transverse x, horizontal x)) := rfl

/-- No norm loss occurs under real complexification and coordinate change. -/
@[simp]
theorem norm_embedSplitSpatial (hd : 2 ≤ d) (v : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) :
    ‖embedSplitSpatial hd v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (BUC.norm_le (norm_nonneg v)).mpr
    intro x
    simpa only [embedSplitSpatial_apply, norm_embed] using v.norm_apply_le (transverse x, horizontal x)
  · apply (BUC.norm_le (norm_nonneg (embedSplitSpatial hd v))).mpr
    rintro ⟨y, z⟩
    simpa only [embedSplitSpatial_apply, transverse_full hd, horizontal_full hd, norm_embed] using
      (embedSplitSpatial hd v).norm_apply_le (full y z)

/-- Evaluation of the embedded data in the semigroup's slice coordinates. -/
@[simp]
theorem spatialSlices_embedSplitSpatial (hd : 2 ≤ d)
    (v : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) (y : ℝ^(d - 1)) (z : ℝ) :
    spatialSlices hd (embedSplitSpatial hd v) y z = embed (v (y, z)) := by
  simp only [spatialSlices_apply, embedSplitSpatial_apply, transverse_full hd, horizontal_full hd]

end

end Planarwave
