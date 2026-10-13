/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearity
import Planarwave.Analysis.NonlinearBootstrapPowers

/-!
# The interpolated nonlinear source estimate for the actual front

Steps 4 and 5 of `lem:key`: derive the C² decay by interpolation, then
substitute it into the actual inverse-modulation nonlinearity. The result
is the improved `M^(7/4) (1+t)^(-5/4)` source estimate. The uniform C⁹
bound remains an explicit prerequisite, to be derived from the parabolic
equation away from the initial time; it is not asserted here.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)

local instance : NormedAddCommGroup (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ) (E := (ℝ^m × ℝ) →L[ℝ] ℝ^n)
local instance : NormedAddCommGroup
    (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ) (E := (ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)

set_option maxHeartbeats 800000 in
/-- The source gains a factor `M^(3/4)` relative to the bootstrap bound.
No small first- or second-derivative bound is assumed: both are obtained
from the C⁹ bound and the already proved logarithmic tracking estimate. -/
theorem exists_frontNonlinearity_interpolated_decay {R K B : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ ε > 0, ∀ (M t : ℝ) (v : BUC (ℝ^m × ℝ) (ℝ^n))
      (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
      (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
      (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ),
      M ∈ Icc 0 ε → 0 ≤ t → ContDiff ℝ 9 (v : (ℝ^m × ℝ) → ℝ^n) →
      (∀ x, HasFDerivAt v (v₁ x) x) → (∀ x, HasFDerivAt v₁ (v₂ x) x) →
      (∀ k ≤ 9, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k v x‖)) →
      (∀ x, ‖iteratedFDeriv ℝ 9 v x‖ ≤ B) → ‖v‖ ≤ R →
      ‖v‖ ≤ K * M / (1 + t) * Real.log (2 + t) →
      ‖s‖ ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)) →
      ‖l‖ ≤ K * M * (1 + t) ^ (-(1 : ℝ)) →
      ‖g‖ ≤ K * M * (1 + t) ^ (-(5 : ℝ) / 4) →
      ‖frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g‖ ≤
        C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
  obtain ⟨H, hH, μ, hμ, hi⟩ := exists_tracking_buc_c2_interpolation_bound
    (E := ℝ^m × ℝ) (F := ℝ^n) hK hB
  obtain ⟨A, hA, hn⟩ := exists_frontInverseModulationNonlinearity_bound (m := m) f D c φ ψ h₁ h₂ hR
  let C := A * (36 * K ^ 2 + H * (3 * K + K ^ 2)) + 1
  refine ⟨C, by dsimp only [C]; positivity, min μ 1, lt_min hμ (by norm_num), ?_⟩
  intro M t v v₁ v₂ s l g hM ht hv hv₁ hv₂ hb hnine hvR hvbound hs hl hg
  have hc2 := hi M t v v₁ v₂ ⟨hM.1, hM.2.trans (min_le_left _ _)⟩ ht hv hv₁ hv₂ hb hvbound hnine
  have hp := unprojected_nonlinearity_decay_product_le (H := H) (norm_nonneg v)
    (by positivity : 0 ≤ ‖v‖ + ‖v₁‖ + ‖v₂‖) (norm_nonneg s) hK hM.1
    (hM.2.trans (min_le_right _ _)) ht
    (by simpa only [div_eq_mul_inv, Real.rpow_neg_one] using hvbound)
    (by simpa only [] using! hc2) hs hl hg
  calc
    _ ≤ A * (‖v‖ ^ 2 + (‖v‖ + ‖v₁‖ + ‖v₂‖) * (‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖)) := by
      simpa only [] using! hn v v₁ v₂ s l g hvR
    _ ≤ A * ((36 * K ^ 2 + H * (3 * K + K ^ 2)) * M ^ ((7 : ℝ) / 4) *
        (1 + t) ^ (-(5 : ℝ) / 4)) := mul_le_mul_of_nonneg_left hp hA.le
    _ ≤ C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
      dsimp only [C]
      nlinarith [mul_nonneg (Real.rpow_nonneg hM.1 ((7 : ℝ) / 4))
        (Real.rpow_nonneg (by linarith : 0 ≤ 1 + t) (-(5 : ℝ) / 4))]

end

end Planarwave
