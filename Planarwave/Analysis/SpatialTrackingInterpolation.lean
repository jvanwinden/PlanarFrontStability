/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialComposition
public import Planarwave.Analysis.TrackingInterpolation

@[expose] public section

/-!
# Tracking interpolation with constructed derivative fields

Apply the paper's ninth-order interpolation estimate to a genuine BUC
derivative tower. Neither boundedness of the standard derivatives nor
the first two BUC derivative witnesses have to be supplied separately.
-/

open Set

namespace Planarwave

noncomputable section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `C^2` decay in Step 4, constructing its derivative fields from
the uniform `C^9` bound and the logarithmic supremum estimate. -/
theorem exists_tracking_spatial_c2_bound {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ ε > 0, ∀ (M t : ℝ) (v : BUC E F),
      M ∈ Icc 0 ε → 0 ≤ t → BUCSpatialBound 9 v B →
      ‖v‖ ≤ K * M / (1 + t) * Real.log (2 + t) →
      BUCSpatialBound 2 v (C * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4)) := by
  obtain ⟨C, hC, ε, hε, hi⟩ := exists_tracking_buc_c2_interpolation_bound (E := E) (F := F) hK hB
  refine ⟨C, hC, ε, hε, ?_⟩
  intro M t v hM ht hv hzero
  have hsmooth := hv.contDiff
  have hbounded : ∀ j ≤ 9, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ j v x‖) := by
    intro j hj
    exact ⟨B, fun _ ⟨x, hx⟩ ↦ hx ▸ hv.norm_iteratedFDeriv_le hj x⟩
  have hnine := hv.norm_iteratedFDeriv_le (j := 9) le_rfl
  obtain ⟨_, q, hq, hd⟩ := hv
  obtain ⟨_, h, _, hdq⟩ := hq
  have hsum := hi M t v q h hM ht hsmooth hd hdq hbounded hzero hnine
  refine ⟨?_, q, ⟨?_, h, ?_, hdq⟩, hd⟩
  · linarith [norm_nonneg q, norm_nonneg h]
  · linarith [norm_nonneg v, norm_nonneg h]
  · change ‖h‖ ≤ _
    linarith [norm_nonneg v, norm_nonneg q]

end

end Planarwave
