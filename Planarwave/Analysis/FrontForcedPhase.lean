/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import Planarwave.Analysis.ForcedPhaseClassical

/-!
# The classical forced phase for the actual front

Use the original transverse diffusivity, adjoint projection, and the
paper's parameter `β = c / (2 d_perp)`. Positivity and the Cole--Hopf
cancellation are discharged from the challenge hypotheses. The source
and its decay bound are supplied by the later nonlinear iteration.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The classical forced phase and uniform zero-order bound for the actual
front coefficients. This is the finite-horizon phase construction in
`lem:xiAP`; it does not assume that a phase solution already exists. -/
theorem exists_front_forced_phase_classical {C : ℝ} (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ →
      (∀ t ∈ Icc 0 T, ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖ ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ ξ σ : ℝ → BUC (ℝ^m) ℝ,
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (ξ t : ℝ^m → ℝ) ∧
          ContDiff ℝ 2 (σ t : ℝ^m → ℝ) ∧
          ‖ξ t‖ ≤ C₀ * M ∧ ‖σ t‖ ≤ (2 * C₀) * M ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) ∧
        (∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * Δ (σ t : ℝ^m → ℝ) y +
            (c / 2) * ‖∇ (σ t : ℝ^m → ℝ) y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t) ∧
        ∀ t ∈ Icc 0 T, t ≤ 1 / 4 → ξ t = 0 ∧ σ t = 0 := by
  have ha := h₃.transverse_low_wavenumber
  have hcancel : d_perp D φ ψ * (c / (2 * d_perp D φ ψ)) = c / 2 := by
    field_simp
  obtain ⟨C₀, hC₀, M₀, hM₀, hex⟩ :=
    exists_delayed_forced_phase_classical (E := ℝ^m) (c / (2 * d_perp D φ ψ)) C hC
  refine ⟨C₀, hC₀, M₀, hM₀, ?_⟩
  intro T M v₀ N hT hM hMM hdecay
  obtain ⟨ξ, σ, hξ, hσc, _, hb, htime, _⟩ := hex (d_perp D φ ψ) c T M
    (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r)) ha hcancel hT hM hMM hdecay
  refine ⟨ξ, σ, hξ, hσc, ?_, htime, ?_⟩
  · intro t ht
    exact ⟨hξ.delayed_contDiff_two ha hT ht, (hb t ht).1,
      (hb t ht).2.1, (hb t ht).2.2.2.1, (hb t ht).2.2.2.2.2⟩
  · intro t ht hquarter
    have hz := hξ.delayed_initial_zero ht hquarter
    refine ⟨hz, ?_⟩
    ext y
    rw [(hb t ht).2.2.2.2.1 y, hz]
    simp

end

end Planarwave
