/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearity
import Planarwave.Analysis.ProjectedNonlinearity
import all Planarwave.Analysis.FrontAdjointRegularity

/-!
# The front's smoothed nonlinearity under the original hypotheses

This is Lemma 4.2 for the actual front nonlinearity and the paper's heat time
`1/8`. Perturbation derivatives are extracted from genuine spatial derivative
fields, and the divergence of the phase gradient is identified with its
Laplacian.

The regular adjoint representative is constructed from the challenge's
spectral hypotheses in `FrontAdjointRegularity`. The final theorem below
discharges this prerequisite and proves the smoothed nonlinear bound without
extra assumptions. Pointwise regularity of the supplied measurable adjoint
is neither needed nor asserted.
-/

open MeasureTheory
open scoped Gradient Laplacian ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The derivative-free estimate for the actual front. The only extra analytic
input is the explicitly stated regular adjoint representative. -/
theorem exists_frontSmoothedNonlinearity_bound_of_adjointRepresentative
    (χ χ₁ χ₂ : ℝ → ℝ^n) (hrep : ψ =ᵐ[volume] χ)
    (hχ₁ : Integrable χ₁) (hχ₂ : Integrable χ₂)
    (hχderiv : ∀ z, HasDerivAt χ (χ₁ z) z)
    (hχderiv₁ : ∀ z, HasDerivAt χ₁ (χ₂ z) z) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ v : BUC (ℝ^m × ℝ) (ℝ^n),
      ∀ v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ σ : ℝ^m → ℝ, ∀ s : BUC (ℝ^m) (ℝ^m),
      ∀ s₁ : BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m), ∀ l g : BUC (ℝ^m) ℝ,
      (∀ x, HasFDerivAt v (v₁ x) x) → (∀ x, HasFDerivAt v₁ (v₂ x) x) →
      (∀ y, s y = ∇ σ y) → (∀ y, HasFDerivAt s (s₁ y) y) → (∀ y, l y = Δ σ y) →
      ‖v‖ ≤ R →
      ‖heatFlowBUC (d_perp D φ ψ) (1 / 8)
        (longitudinalPairing ψ h₃.integrable
          (frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g))‖ ≤
        C * ‖v‖ * (‖v‖ + ‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖) := by
  have hχ : Integrable χ := h₃.integrable.congr hrep
  obtain ⟨C, hC, hb⟩ := exists_smoothedProjectedNonlinearity_bound f
    (h₁.smooth.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) D c
    (d_perp D φ ψ) hχ hχ₁ hχ₂ hχderiv hχderiv₁
    (frontSplitProfileBUC (m := m) f D c φ h₂) hR h₃.transverse_low_wavenumber
    (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨C, hC, fun v v₁ v₂ σ s s₁ l g hv₁ hv₂ hs hs₁ hl hv ↦ ?_⟩
  have hdiv : divergenceBUC s₁ = l := by
    ext y
    rw [divergenceBUC_gradient σ s s₁ hs hs₁ y, hl y]
  rw [longitudinalPairing_congr_ae h₃.integrable hχ hrep]
  simpa only [frontInverseModulationNonlinearity, hdiv] using
    hb v (BUC.longitudinalDerivativeField v₁) (BUC.longitudinalSecondDerivativeField v₂)
      (BUC.transverseDerivativeField v₁) (BUC.mixedDerivativeField v₂) s s₁ g
      (BUC.hasDerivAt_longitudinalDerivativeField v v₁ hv₁)
      (BUC.hasDerivAt_longitudinalSecondDerivativeField v₁ v₂ hv₂)
      (BUC.hasFDerivAt_transverseDerivativeField v v₁ hv₁)
      (BUC.hasFDerivAt_mixedDerivativeField v₁ v₂ hv₂) hs₁ hv

/-- Lemma 4.2 for the actual front, with adjoint regularity discharged from
the original parabolic, front, and spectral hypotheses. The constant is
chosen uniformly before the perturbation, phase, and forcing fields. -/
theorem exists_frontSmoothedNonlinearity_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ v : BUC (ℝ^m × ℝ) (ℝ^n),
      ∀ v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ σ : ℝ^m → ℝ, ∀ s : BUC (ℝ^m) (ℝ^m),
      ∀ s₁ : BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m), ∀ l g : BUC (ℝ^m) ℝ,
      (∀ x, HasFDerivAt v (v₁ x) x) → (∀ x, HasFDerivAt v₁ (v₂ x) x) →
      (∀ y, s y = ∇ σ y) → (∀ y, HasFDerivAt s (s₁ y) y) → (∀ y, l y = Δ σ y) →
      ‖v‖ ≤ R →
      ‖heatFlowBUC (d_perp D φ ψ) (1 / 8)
        (longitudinalPairing ψ h₃.integrable
          (frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g))‖ ≤
        C * ‖v‖ * (‖v‖ + ‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖) := by
  obtain ⟨χ, χ₁, χ₂, hrep, _, hi₁, hi₂, _, _, hd₁, hd₂, _⟩ :=
    exists_frontAdjoint_regularRepresentative f D c φ ψ h₁ h₂ h₃
  exact exists_frontSmoothedNonlinearity_bound_of_adjointRepresentative f D c φ ψ h₁ h₂ h₃
    χ χ₁ χ₂ hrep hi₁ hi₂ hd₁ hd₂ hR

end

end Planarwave
