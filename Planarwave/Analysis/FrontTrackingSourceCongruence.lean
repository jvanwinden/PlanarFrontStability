/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingSystem
import all Planarwave.Analysis.FrontNonlinearityContinuity

/-!
# Compatibility of nonlinear sources on overlapping tracking intervals

The source does not depend on the choice of genuine spatial derivative fields.
Consequently equal physical solutions, phases, and forcing give equal sources.
At time zero the vanishing phase coefficients replace derivative uniqueness,
so this compatibility also holds for rough initial BUC data.
-/

open Set
open scoped Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- The choice of first and second BUC derivative fields does not affect the
nonlinear source. Only equality of their underlying differentiable functions
is needed, not equality of the derivative fields as supplied data. -/
theorem frontInverseModulationNonlinearity_congr_of_derivatives
    {v w : BUC (ℝ^m × ℝ) (ℝ^n)}
    {v₁ w₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n)}
    {v₂ w₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)}
    {s r : BUC (ℝ^m) (ℝ^m)} {l k g h : BUC (ℝ^m) ℝ}
    (hv : v = w)
    (hv₁ : ∀ x, HasFDerivAt v (v₁ x) x) (hv₂ : ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (hw₁ : ∀ x, HasFDerivAt w (w₁ x) x) (hw₂ : ∀ x, HasFDerivAt w₁ (w₂ x) x)
    (hs : s = r) (hl : l = k) (hg : g = h) :
    frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g =
      frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ w w₁ w₂ r k h := by
  subst w
  have hfirst : v₁ = w₁ := BUC.ext fun x ↦ (hv₁ x).unique (hw₁ x)
  subst w₁
  have hsecond : v₂ = w₂ := BUC.ext fun x ↦ (hv₂ x).unique (hw₂ x)
  rw [hsecond, hs, hl, hg]

/-- During the zero-phase interval, equal perturbations give equal sources
without any assumptions on the chosen spatial derivative fields. -/
theorem frontInverseModulationNonlinearity_congr_zero_phase
    {v w : BUC (ℝ^m × ℝ) (ℝ^n)}
    (v₁ w₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (v₂ w₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (hv : v = w) :
    frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ 0 0 0 =
      frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ w w₁ w₂ 0 0 0 := by
  rw [frontInverseModulationNonlinearity_zero_phase,
    frontInverseModulationNonlinearity_zero_phase, hv]

/-- Pointwise-in-time source compatibility for physical data. The phase
gradient and Laplacian agree because they are genuine derivatives of equal
phases. This lemma does not assume that either source already belongs to a
self-consistent tracking system. -/
theorem frontPhysicalNonlinearSource_congr
    {u w : BUC (ℝ^d) (ℝ^n)} {a : ℝ}
    {σ τ : BUC (ℝ^(d - 1)) ℝ}
    {v₁ w₁ : BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n)}
    {v₂ w₂ : BUC (ℝ^(d - 1) × ℝ)
      ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n)}
    {s r : BUC (ℝ^(d - 1)) (ℝ^(d - 1))} {l k g h : BUC (ℝ^(d - 1)) ℝ}
    (hu : u = w) (hσ : σ = τ) (hg : g = h)
    (hv₁ : ∀ x, HasFDerivAt
      (frontInverseModulatedPerturbation f D c φ h₂ hd u a σ) (v₁ x) x)
    (hv₂ : ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (hw₁ : ∀ x, HasFDerivAt
      (frontInverseModulatedPerturbation f D c φ h₂ hd w a τ) (w₁ x) x)
    (hw₂ : ∀ x, HasFDerivAt w₁ (w₂ x) x)
    (hs : ∀ y, s y = ∇ (σ : ℝ^(d - 1) → ℝ) y)
    (hr : ∀ y, r y = ∇ (τ : ℝ^(d - 1) → ℝ) y)
    (hl : ∀ y, l y = Δ (σ : ℝ^(d - 1) → ℝ) y)
    (hk : ∀ y, k y = Δ (τ : ℝ^(d - 1) → ℝ) y) :
    frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
        (frontInverseModulatedPerturbation f D c φ h₂ hd u a σ) v₁ v₂ s l g =
      frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
        (frontInverseModulatedPerturbation f D c φ h₂ hd w a τ) w₁ w₂ r k h := by
  apply frontInverseModulationNonlinearity_congr_of_derivatives f D c φ ψ h₁ h₂
    (by rw [hu, hσ]) hv₁ hv₂ hw₁ hw₂ ?_ ?_ hg
  · exact BUC.ext fun y ↦ by rw [hs, hr, hσ]
  · exact BUC.ext fun y ↦ by rw [hl, hk, hσ]

namespace FrontTrackingSystem

variable {f D c φ ψ h₁ h₂ h₃ hd} {T S t : ℝ}
  (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T)

/-- Compare an established tracking source with freshly constructed source
data at one shared time. Genuine jets are needed only at positive times;
zero phase coefficients handle the rough initial datum. -/
theorem source_eq_of_physical_fields_eq
    (ht : t ∈ Icc 0 T)
    {u : BUC (ℝ^d) (ℝ^n)} {σ : BUC (ℝ^(d - 1)) ℝ}
    {v₁ : BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n)}
    {v₂ : BUC (ℝ^(d - 1) × ℝ)
      ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n)}
    {s : BUC (ℝ^(d - 1)) (ℝ^(d - 1))} {l g : BUC (ℝ^(d - 1)) ℝ}
    (hu : X.u t = u) (hσ : X.σ t = σ) (hg : X.forcing t = g)
    (hv₁ : 0 < t → ∀ x, HasFDerivAt
      (frontInverseModulatedPerturbation f D c φ h₂ hd u (c * t) σ) (v₁ x) x)
    (hv₂ : 0 < t → ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (hs : ∀ y, s y = ∇ (σ : ℝ^(d - 1) → ℝ) y)
    (hl : ∀ y, l y = Δ (σ : ℝ^(d - 1) → ℝ) y) :
    X.N t = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
      (frontInverseModulatedPerturbation f D c φ h₂ hd u (c * t) σ) v₁ v₂ s l g := by
  rw [X.source_eq t ht]
  change frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
    (frontInverseModulatedPerturbation f D c φ h₂ hd (X.u t) (c * t) (X.σ t))
    (X.v₁ t) (X.v₂ t) (X.s t) (X.l t) (X.forcing t) = _
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · have htz : t = 0 := ht0.symm
    obtain ⟨hsX, hlX, hgX⟩ := X.initial_zero ht (by rw [htz]; norm_num)
    have hsEq : X.s t = s := BUC.ext fun y ↦ by rw [X.gradient_eq t ht, hs, hσ]
    have hlEq : X.l t = l := BUC.ext fun y ↦ by rw [X.laplacian_eq t ht, hl, hσ]
    rw [← hsEq, ← hlEq, ← hg, hsX, hlX, hgX]
    apply frontInverseModulationNonlinearity_congr_zero_phase f D c φ ψ h₁ h₂
    rw [hu, hσ]
  · exact frontPhysicalNonlinearSource_congr f D c φ ψ h₁ h₂ hd hu hσ hg
      (X.first_derivative t ⟨ht0, ht.2⟩) (X.second_derivative t ⟨ht0, ht.2⟩)
      (hv₁ ht0) (hv₂ ht0) (X.gradient_eq t ht) hs (X.laplacian_eq t ht) hl

/-- Two tracking bundles with the same physical data, phase and forcing at a
shared time have the same source, including at the rough initial time. -/
theorem source_eq_of_fields_eq (Y : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd S)
    (ht : t ∈ Icc 0 T) (hs : t ∈ Icc 0 S)
    (hu : X.u t = Y.u t) (hσ : X.σ t = Y.σ t) (hg : X.forcing t = Y.forcing t) :
    X.N t = Y.N t := by
  rw [Y.source_eq t hs]
  exact X.source_eq_of_physical_fields_eq ht hu hσ hg
    (fun hp ↦ Y.first_derivative t ⟨hp, hs.2⟩)
    (fun hp ↦ Y.second_derivative t ⟨hp, hs.2⟩)
    (Y.gradient_eq t hs) (Y.laplacian_eq t hs)

end FrontTrackingSystem

end

end Planarwave
