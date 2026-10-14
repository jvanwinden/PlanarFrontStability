/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearityContinuity
import Planarwave.Analysis.BUCSpatialBounds
import Planarwave.Analysis.NonlinearBootstrapPowers

/-!
# The improved nonlinear source estimate with rough initial data

Step 5 of the paper's a priori argument combines logarithmic tracking, the
interpolated C² bound, and the phase estimates. The initial quarter interval
does not require spatial derivatives: all their coefficients vanish there.
Thus the estimate is valid at time zero for arbitrary BUC initial data.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)

local instance : NormedAddCommGroup (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ) (E := (ℝ^m × ℝ) →L[ℝ] ℝ^n)
local instance : NormedAddCommGroup
    (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ)
    (E := (ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)

set_option maxHeartbeats 800000 in
/-- The constants are chosen before the solution, derivative fields, phase,
and time. Derivative bounds are needed only after the initial zero-phase
interval. In particular, no spatial smoothness of the initial datum is used. -/
theorem exists_front_cutoff_nonlinearity_decay {K H : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) :
    ∃ C > 0, ∀ {M t : ℝ}, 0 ≤ M → M ≤ 1 → 0 ≤ t →
      ∀ (v : BUC (ℝ^m × ℝ) (ℝ^n))
        (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
        (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
        (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ),
      ‖v‖ ≤ K * M / (1 + t) * Real.log (2 + t) →
      ‖s‖ ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)) →
      ‖l‖ ≤ K * M * (1 + t) ^ (-(1 : ℝ)) →
      ‖g‖ ≤ K * M * (1 + t) ^ (-(5 : ℝ) / 4) →
      (t ≤ 1 / 4 → s = 0 ∧ l = 0 ∧ g = 0) →
      (1 / 4 < t →
        BUCSpatialBound 2 v (H * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4)) ∧
        (∀ x, HasFDerivAt v (v₁ x) x) ∧ (∀ x, HasFDerivAt v₁ (v₂ x) x)) →
      ‖frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g‖ ≤
        C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
  obtain ⟨C₀, hC₀, hb⟩ :=
    exists_frontInverseModulationNonlinearity_bound (m := m) f D c φ ψ h₁ h₂ hK
  let A : ℝ := 36 * K ^ 2 + (3 * H) * (3 * K + K ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1 + C₀ * A, by positivity, ?_⟩
  intro M t hM hM1 ht v v₁ v₂ s l g hv hs hl hg hzero hlate
  have hden : 0 < 1 + t := by linarith
  have hvK : ‖v‖ ≤ K := by
    have hlog : Real.log (2 + t) ≤ 1 + t := by
      have := Real.log_le_sub_one_of_pos (show 0 < 2 + t by linarith)
      linarith
    calc
      ‖v‖ ≤ K * M / (1 + t) * Real.log (2 + t) := hv
      _ ≤ K * M / (1 + t) * (1 + t) := by gcongr
      _ = K * M := div_mul_cancel₀ _ hden.ne'
      _ ≤ K := by nlinarith
  have hv' : ‖v‖ ≤ K * M * (1 + t) ^ (-(1 : ℝ)) * Real.log (2 + t) := by
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hv
  have hfinish (V : ℝ) (hV0 : 0 ≤ V)
      (hV : V ≤ (3 * H) * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4))
      (hN : ‖frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g‖ ≤
        C₀ * (‖v‖ ^ 2 + V * (‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖))) :
      ‖frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g‖ ≤
        (1 + C₀ * A) * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
    have hp := unprojected_nonlinearity_decay_product_le (norm_nonneg v) hV0
      (norm_nonneg s) hK hM hM1 ht hv' hV hs hl hg
    calc
      _ ≤ C₀ * (‖v‖ ^ 2 + V * (‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖)) := hN
      _ ≤ C₀ * (A * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hp hC₀.le
      _ = (C₀ * A) * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by ring
      _ ≤ _ := by gcongr; linarith
  by_cases hearly : t ≤ 1 / 4
  · obtain ⟨hs0, hl0, hg0⟩ := hzero hearly
    apply hfinish 0 (le_refl _) (by positivity)
    simpa only [hs0, hl0, hg0, norm_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, mul_zero, zero_mul] using hb v v₁ v₂ s l g hvK
  · obtain ⟨hbv, hd₁, hd₂⟩ := hlate (lt_of_not_ge hearly)
    have hb₁ := hbv.derivative hd₁
    have hb₂ := hb₁.derivative hd₂
    refine hfinish (‖v‖ + ‖v₁‖ + ‖v₂‖) (by positivity) ?_ (hb v v₁ v₂ s l g hvK)
    have hvb := hbv.norm_le
    have hv₁b := hb₁.norm_le
    have hv₂b := hb₂.norm_le
    nlinarith

end

end Planarwave
