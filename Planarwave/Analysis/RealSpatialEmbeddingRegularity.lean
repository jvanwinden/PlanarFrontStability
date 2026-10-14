/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.RealSpatialEmbedding
public import Planarwave.Analysis.BUCLinearPullback

/-!
# Genuine spatial BUC jets under real-to-complex coordinate embedding

The time-continuous derivative hierarchy of the real inverse-modulated
perturbation transfers to the full-coordinate complex field used by the
front semigroup. This uses the actual bounded linear coordinate maps.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ}

/-- Real complexification and the fixed split-coordinate change preserve
the genuine time-continuous spatial BUC derivative hierarchy. -/
theorem BUCSpatialRegularOn.embedSplitSpatial (hd : 2 ≤ d)
    {s : Set ℝ} {k : ℕ} {v : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)}
    (hv : BUCSpatialRegularOn s k v) :
    BUCSpatialRegularOn s k (fun t ↦ Planarwave.embedSplitSpatial hd (v t)) := by
  exact (hv.precompCLM (coordinateEquiv hd).toContinuousLinearMap).postcompCLM
    realStateEmbeddingCLM

end

end Planarwave
