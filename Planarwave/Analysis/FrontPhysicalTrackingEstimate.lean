/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontPhysicalDuhamel
import all Planarwave.Analysis.FrontTrackingCriticalDecomposition

/-!
# Logarithmic tracking for the actual physical solution

Steps 2 and 3 of the paper's a priori estimate now bound the actual
inverse-modulated physical solution, not an independently constructed
semigroup response. The physical equation and phase equation produce the
Duhamel identity. The delayed forcing cancels its neutral component.

The nonlinear source bound and the weighted phase derivative bounds remain
bootstrap hypotheses. No Duhamel identity or equation for the modulated
perturbation is assumed.
-/

open Set
open scoped Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- The paper's logarithmic tracking estimate for the actual physical
perturbation. Its constant is chosen before the horizon, amplitude, and
solution paths. Genuine derivatives identify the supplied nonlinear source
only at positive interior times; continuity handles both endpoints. -/
theorem exists_front_physical_tracking_decay (K : ℝ) :
    ∃ C > 0, ∀ (T M : ℝ)
      (u : ℝ → BUC (ℝ^d) (ℝ^n)) (σ : ℝ → BUC (ℝ^(d - 1)) ℝ)
      (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
      (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
      (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ)
      (v₁ : ℝ → BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
      (v₂ : ℝ → BUC (ℝ^(d - 1) × ℝ)
        ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ 1 →
      ContinuousOn u (Icc 0 T) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u →
      ContinuousOn σ (Icc 0 T) → BUCSpatialRegularOn (Ioo 0 T) 2 σ →
      ContinuousOn N (Icc 0 T) → ContinuousOn s (Icc 0 T) → ContinuousOn l (Icc 0 T) →
      (frontInverseModulatedPerturbation f D c φ h₂ hd (u 0) (c * 0) (σ 0) = v₀) →
      ‖v₀‖ ≤ M →
      (∀ t ∈ Ioo 0 T, ∀ y, s t y = ∇ (σ t : ℝ^(d - 1) → ℝ) y) →
      (∀ t ∈ Ioo 0 T, ∀ y, l t y = Δ (σ t : ℝ^(d - 1) → ℝ) y) →
      (∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
        (d_perp D φ ψ * l t y + (c / 2) * ‖s t y‖ ^ 2 -
          frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t) →
      (∀ t ∈ Ioo 0 T, ∀ x, HasFDerivAt
        (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)) (v₁ t x) x) →
      (∀ t ∈ Ioo 0 T, ∀ x, HasFDerivAt (v₁ t) (v₂ t x) x) →
      (∀ t ∈ Ioo 0 T, N t = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
        (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t))
        (v₁ t) (v₂ t) (s t) (l t) (frontDelayedForcing f D c φ ψ h₃ v₀ N t)) →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      (∀ r ∈ Icc 0 T, ‖s r‖ ≤ K * M * (1 + r) ^ (-(1 / 2 : ℝ))) →
      (∀ r ∈ Icc 0 T, ‖l r‖ ≤ K * M * (1 + r) ^ (-(1 : ℝ))) →
      ∀ t ∈ Icc 0 T,
        ‖frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)‖ ≤
          (C * M / (1 + t)) * Real.log (2 + t) := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_frontTrackingSpatialDuhamel_decay f D c φ ψ h₃ h₁ h₂ hd K
  refine ⟨C, hC, ?_⟩
  intro T M u σ v₀ N s l v₁ v₂ hT hM hM1 hu hm hσc hσreg hNc hsc hlc
    hinit hv₀ hgrad hlap hphase hv₁ hv₂ hNid hN hs hl t ht
  have heq := frontInverseModulatedPerturbation_eq_realOrbit_add_duhamel
    f D c φ ψ h₁ h₂ h₃ hd hT u hu hm σ hσc hσreg s l
    (frontDelayedForcing f D c φ ψ h₃ v₀ N) hsc hlc
    (continuous_frontDelayedForcing f D c φ ψ h₃ v₀ N).continuousOn
    hgrad hlap hphase N hNc v₁ v₂ hv₁ hv₂ hNid ht
  rw [← norm_embedSplitSpatial hd, heq, hinit]
  exact hdecay T M v₀ N s l hM hM1 hv₀ hNc hsc hlc hN hs hl t ht

end

end Planarwave
