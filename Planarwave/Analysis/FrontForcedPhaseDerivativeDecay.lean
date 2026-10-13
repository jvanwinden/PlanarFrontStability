/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingDecay
import all Planarwave.Analysis.FrontDelayedForcing
import all Planarwave.Analysis.FrontForcedPhaseFirstDerivativeBounds
import all Planarwave.Analysis.FrontForcedPhaseSecondDerivativeBounds
import Planarwave.Analysis.ForcedPhaseDerivativeDecay

/-!
# Weighted phase decay for the actual front

The source estimate at the start of `lem:key` implies the weighted
gradient and Laplacian estimates from Step 1. The delayed forcing is the
actual adjoint-projected source; its C² decay is derived rather than
assumed. Closing the source bound with the coupled system remains separate.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The actual front's classical forced phase has the value, gradient,
and Laplacian bounds in Step 1, from undifferentiated source decay only.
The constants depend on the front, not on the data or time horizon. -/
theorem exists_front_forced_phase_derivative_decay_of_source_decay :
    ∃ C₀ > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M →
      (∀ t ∈ Icc 0 T, ‖N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC (ℝ^m) ℝ) (s : ℝ → BUC (ℝ^m) (ℝ^m)) (L : ℝ → BUC (ℝ^m) ℝ),
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧ ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧
        σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : ℝ^m → ℝ) ∧
          (∀ y, s t y = ∇ (σ t : ℝ^m → ℝ) y) ∧ (∀ y, L t y = Δ (σ t : ℝ^m → ℝ) y) ∧
          ‖σ t‖ ≤ C₀ * M ∧ ‖s t‖ ≤ C₀ * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
          ‖L t‖ ≤ C₀ * M * (1 + t) ^ (-(1 : ℝ)) ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * L t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  have ha := h₃.transverse_low_wavenumber
  have hcancel : d_perp D φ ψ * (c / (2 * d_perp D φ ψ)) = c / 2 := by field_simp
  obtain ⟨C₀, hC₀, M₀, hM₀, hex⟩ := exists_delayed_forced_phase_derivative_decay (E := ℝ^m)
    (d_perp D φ ψ) (c / (2 * d_perp D φ ψ)) (frontForcingC2DecayConstant D φ ψ (5 / 4))
    ha (frontForcingC2DecayConstant_pos D φ ψ (5 / 4))
  refine ⟨C₀, hC₀, M₀, hM₀, ?_⟩
  intro T M v₀ N hT hM hMM hv₀ hN
  apply hex c T M (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r)) hcancel hT hM hMM
  intro t ht
  simpa only [neg_div, frontDelayedForcing, frontDelayedForcingFDeriv,
    frontDelayedForcingFDeriv2] using! norm_frontDelayedForcing_c2_decay_le f D c φ ψ h₃
    (by norm_num : (0 : ℝ) ≤ 5 / 4) v₀ N hM hv₀ (by simpa only [neg_div] using hN) ht

end

end Planarwave
