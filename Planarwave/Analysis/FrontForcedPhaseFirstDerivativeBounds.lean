/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import Planarwave.Analysis.ForcedPhaseFirstDerivativeBounds

/-!
# First-order phase estimates for the actual front

Specialize the C¹ Cole--Hopf estimate and the constructed gradient to
the original transverse diffusivity and adjoint-projected forcing.
The forcing's C¹ block bound uses no derivatives of its nonlinear source.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The genuine first derivative of the front's delayed forcing. -/
def frontDelayedForcingFDeriv (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ) :=
  delayedHeatForcingFDeriv h₃.transverse_low_wavenumber (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))

theorem continuous_frontDelayedForcingFDeriv (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) :
    Continuous (frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N) :=
  continuous_delayedHeatForcingFDeriv h₃.transverse_low_wavenumber _ _

theorem hasFDerivAt_frontDelayedForcing (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (t : ℝ) (y : ℝ^m) :
    HasFDerivAt (frontDelayedForcing f D c φ ψ h₃ v₀ N t)
      (frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N t y) y :=
  hasFDerivAt_delayedHeatForcing h₃.transverse_low_wavenumber _ _ t y

/-- A derivative-free source bound controls the actual C¹ forcing norm
on the next block, after the fixed positive heat smoothing time. -/
theorem norm_frontDelayedForcing_c1_block_le (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (k : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ∀ r ∈ Icc (k : ℝ) ((k : ℝ) + 1), ‖N r‖ ≤ M) :
    max ‖frontDelayedForcing f D c φ ψ h₃ v₀ N ((k : ℝ) + 1 + τ)‖
        ‖frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N ((k : ℝ) + 1 + τ)‖ ≤
      trackingCutoff τ * (max 1 (heatScale (d_perp D φ ψ) (1 / 8))⁻¹ *
        ((∫ z, ‖ψ z‖) * M)) := by
  apply norm_delayedHeatForcing_c1_block_le h₃.transverse_low_wavenumber _ _ k hτ
  intro r hr
  exact (norm_longitudinalPairing_le ψ h₃.integrable (N r)).trans
    (mul_le_mul_of_nonneg_left (hN r hr) (integral_nonneg fun z ↦ norm_nonneg (ψ z)))

/-- Under the paper's C¹ forcing decay assumption, construct a classical
phase and its actual time-continuous BUC gradient with uniform bounds.
The constants depend on the front and the forcing constant, not on the
time horizon, data, or nonlinear source. -/
theorem exists_front_forced_phase_classical_c1 {C : ℝ} (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ →
      (∀ t ∈ Icc 0 T, max ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖
          ‖frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N t‖ ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC (ℝ^m) ℝ) (q : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ))
        (s : ℝ → BUC (ℝ^m) (ℝ^m)),
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧ Continuous q ∧ ContinuousOn s (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : ℝ^m → ℝ) ∧
          (∀ y, HasFDerivAt (ξ t) (q t y) y) ∧ (∀ y, s t y = ∇ (σ t : ℝ^m → ℝ) y) ∧
          max ‖ξ t‖ ‖q t‖ ≤ C₀ * M ∧ max ‖σ t‖ ‖s t‖ ≤ (2 * C₀) * M ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * Δ (σ t : ℝ^m → ℝ) y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  have ha := h₃.transverse_low_wavenumber
  have hcancel : d_perp D φ ψ * (c / (2 * d_perp D φ ψ)) = c / 2 := by field_simp
  obtain ⟨C₀, hC₀, M₀, hM₀, hex⟩ :=
    exists_delayed_forced_phase_classical_c1 (E := ℝ^m) (c / (2 * d_perp D φ ψ)) C hC
  refine ⟨C₀, hC₀, M₀, hM₀, ?_⟩
  intro T M v₀ N hT hM hMM hdecay
  exact hex (d_perp D φ ψ) c T M (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r)) ha hcancel hT hM hMM hdecay

end

end Planarwave
