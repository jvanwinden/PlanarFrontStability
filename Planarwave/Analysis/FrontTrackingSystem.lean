/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontPhysicalTrackingEstimate
import all Planarwave.Analysis.FrontTrackingInitialZero

/-!
# The finite-slab coupled tracking equations

Bundle the equations and genuine derivative data used in the paper's a priori
argument. No decay estimate is part of this bundle. In particular, defining
this type does not assert existence of self-consistent tracking solutions.
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

/-- Equations for an actual physical tracking solution on `[0,T]`, with
the nonlinear source fed back into its own delayed forcing. -/
structure FrontTrackingSystem (T : ℝ) where
  nonneg : 0 ≤ T
  u : ℝ → BUC (ℝ^d) (ℝ^n)
  ξ : ℝ → BUC (ℝ^(d - 1)) ℝ
  σ : ℝ → BUC (ℝ^(d - 1)) ℝ
  s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))
  l : ℝ → BUC (ℝ^(d - 1)) ℝ
  v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)
  N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)
  v₁ : ℝ → BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n)
  v₂ : ℝ → BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n)
  physical_continuous : ContinuousOn u (Icc 0 T)
  physical_mild : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u
  phase_regular : BUCSpatialRegularOn (Icc 0 T) 2 σ
  gradient_continuous : ContinuousOn s (Icc 0 T)
  laplacian_continuous : ContinuousOn l (Icc 0 T)
  source_continuous : ContinuousOn N (Icc 0 T)
  initial : frontInverseModulatedPerturbation f D c φ h₂ hd (u 0) (c * 0) (σ 0) = v₀
  coleHopf_mild : IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
    (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T
  coleHopf_eq : ∀ t ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t
  gradient_eq : ∀ t ∈ Icc 0 T, ∀ y, s t y = ∇ (σ t : ℝ^(d - 1) → ℝ) y
  laplacian_eq : ∀ t ∈ Icc 0 T, ∀ y, l t y = Δ (σ t : ℝ^(d - 1) → ℝ) y
  phase_pde : ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
    (d_perp D φ ψ * l t y + (c / 2) * ‖s t y‖ ^ 2 - frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t
  first_derivative : ∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt
    (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)) (v₁ t x) x
  second_derivative : ∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt (v₁ t) (v₂ t x) x
  source_eq : ∀ t ∈ Icc 0 T, N t = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
    (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t))
    (v₁ t) (v₂ t) (s t) (l t) (frontDelayedForcing f D c φ ψ h₃ v₀ N t)

namespace FrontTrackingSystem

variable {f D c φ ψ h₁ h₂ h₃ hd} {T : ℝ}
  (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T)

/-- The actual perturbation, not an independent semigroup response. -/
def perturbation (t : ℝ) : BUC (ℝ^(d - 1) × ℝ) (ℝ^n) :=
  frontInverseModulatedPerturbation f D c φ h₂ hd (X.u t) (c * t) (X.σ t)

def forcing : ℝ → BUC (ℝ^(d - 1)) ℝ := frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N

omit [Nontrivial (ℝ^n)] in
theorem initial_zero {t : ℝ} (ht : t ∈ Icc 0 T) (hq : t ≤ 1 / 4) :
    X.s t = 0 ∧ X.l t = 0 ∧ X.forcing t = 0 :=
  frontTrackingCoefficients_initial_zero f D c φ ψ h₃ X.coleHopf_mild ht hq
    (X.coleHopf_eq t ht) (X.s t) (X.l t) (X.gradient_eq t ht) (X.laplacian_eq t ht)

/-- Restriction to a shorter slab preserves the same coupled equations.
The supplied source and its delayed forcing are not changed. -/
def mono {S : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd S where
  nonneg := hS
  u := X.u
  ξ := X.ξ
  σ := X.σ
  s := X.s
  l := X.l
  v₀ := X.v₀
  N := X.N
  v₁ := X.v₁
  v₂ := X.v₂
  physical_continuous := X.physical_continuous.mono (Icc_subset_Icc le_rfl hST)
  physical_mild := X.physical_mild.mono hST
  phase_regular := X.phase_regular.mono (Icc_subset_Icc le_rfl hST)
  gradient_continuous := X.gradient_continuous.mono (Icc_subset_Icc le_rfl hST)
  laplacian_continuous := X.laplacian_continuous.mono (Icc_subset_Icc le_rfl hST)
  source_continuous := X.source_continuous.mono (Icc_subset_Icc le_rfl hST)
  initial := X.initial
  coleHopf_mild := X.coleHopf_mild.mono hST
  coleHopf_eq := fun t ht ↦ X.coleHopf_eq t ⟨ht.1, ht.2.trans hST⟩
  gradient_eq := fun t ht ↦ X.gradient_eq t ⟨ht.1, ht.2.trans hST⟩
  laplacian_eq := fun t ht ↦ X.laplacian_eq t ⟨ht.1, ht.2.trans hST⟩
  phase_pde := fun t ht ↦ X.phase_pde t ⟨ht.1, ht.2.trans_le hST⟩
  first_derivative := fun t ht ↦ X.first_derivative t ⟨ht.1, ht.2.trans hST⟩
  second_derivative := fun t ht ↦ X.second_derivative t ⟨ht.1, ht.2.trans hST⟩
  source_eq := fun t ht ↦ X.source_eq t ⟨ht.1, ht.2.trans hST⟩

end FrontTrackingSystem

end

end Planarwave
