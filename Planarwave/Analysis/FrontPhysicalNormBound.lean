/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearity

/-!
# Physical bounds from inverse-modulated perturbations

The spatial coordinate splitting and modulation shear are bijections, hence
preserve the BUC supremum norm exactly. A bound on the inverse-modulated
perturbation therefore bounds the physical solution independently of the
size or derivatives of the phase. This supplies the physical boundedness
input to parabolic smoothing and the continuation criterion.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- Coordinate splitting preserves the physical supremum norm, even though
the Euclidean and product spatial norms are different. -/
theorem norm_frontCoordinatePullback {d n : ℕ} (hd : 2 ≤ d)
    (u : BUC (ℝ^d) (ℝ^n)) :
    ‖u.comp (coordinateEquiv hd).symm
      (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous‖ = ‖u‖ := by
  apply le_antisymm (BUC.norm_comp_le _ _ _)
  apply (BUC.norm_le (norm_nonneg _)).mpr
  intro x
  obtain ⟨y, rfl⟩ := (coordinateEquiv hd).symm.surjective x
  exact (u.comp (coordinateEquiv hd).symm
    (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous).norm_apply_le y

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₂ : IsSmoothFront f D c φ)

/-- Tracking the inverse-modulated perturbation bounds the physical BUC
solution, with no phase smallness or regularity assumption beyond BUC. -/
theorem norm_le_frontInverseModulatedPerturbation_add_profile {d : ℕ} (hd : 2 ≤ d)
    (u : BUC (ℝ^d) (ℝ^n)) (a : ℝ) (σ : BUC (ℝ^(d - 1)) ℝ) :
    ‖u‖ ≤ ‖frontInverseModulatedPerturbation f D c φ h₂ hd u a σ‖ +
      ‖frontSplitProfileBUC (m := d - 1) f D c φ h₂‖ := by
  let w := modulationShift a σ (u.comp (coordinateEquiv hd).symm
    (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous)
  let p := frontSplitProfileBUC (m := d - 1) f D c φ h₂
  have hw : ‖w‖ = ‖u‖ := by
    dsimp only [w]
    rw [norm_modulationShift, norm_frontCoordinatePullback]
  change ‖u‖ ≤ ‖w - p‖ + ‖p‖
  calc
    ‖u‖ = ‖(w - p) + p‖ := by rw [sub_add_cancel, hw]
    _ ≤ ‖w - p‖ + ‖p‖ := norm_add_le _ _

end

end Planarwave
