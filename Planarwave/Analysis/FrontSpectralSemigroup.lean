/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontCriticalSemigroup
import all Planarwave.Analysis.FrontCompactSemigroupBounds
import Planarwave.Analysis.SemigroupIntertwining

/-!
# Invariance of the front's critical spectral splitting

The critical projection intertwines the full generator, not just its critical eigenline.
Consequently it commutes with the longitudinal semigroup, its complementary kernel is invariant,
and critical evolution can be extracted on either side. These are the splitting identities
underlying the complementary estimate in Lemma 2.3; no complementary decay is assumed or claimed.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The critical projection is also a left eigenmap of the common-domain pencil. -/
theorem eventually_frontCriticalProjection_leftEigenmap :
    ∀ᶠ q : ℂ in 𝓝 0, ∀ v : ComplexBUC2 (ℂ^n),
      frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q
          (frontLongitudinalPencil f D c φ h₁ h₂ q v) =
        frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q •
          frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q (ComplexBUC2.value (ℂ^n) v) := by
  filter_upwards [eventually_frontCriticalProjection_spectralSplitting f D c φ ψ h₁ h₂ h₃]
    with q hq
  intro v
  have hz : frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q
      (frontCriticalShiftedPencil f D c φ ψ h₁ h₂ h₃ q v) = 0 := by
    change frontCriticalShiftedPencil f D c φ ψ h₁ h₂ h₃ q v ∈
      LinearMap.ker (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q).toLinearMap
    rw [hq.2]
    exact ⟨v, rfl⟩
  change frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q
    (frontLongitudinalPencil f D c φ h₁ h₂ q v -
      frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q • ComplexBUC2.value (ℂ^n) v) = 0 at hz
  simpa only [map_sub, map_smul, sub_eq_zero] using! hz

variable [Nontrivial (ℝ^n)]

/-- Near zero the critical spectral projection commutes with the full longitudinal evolution. -/
theorem eventually_frontPencilSemigroup_comp_criticalProjection :
    ∀ᶠ q : ℂ in 𝓝 0, ∀ t : NNReal,
      (frontPencilC0Semigroup f D c φ h₁ h₂ q t).comp
          (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q) =
        (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q).comp
          (frontPencilC0Semigroup f D c φ h₁ h₂ q t) := by
  filter_upwards [eventually_frontCriticalProjection_eigenrange f D c φ ψ h₁ h₂ h₃,
    eventually_frontCriticalProjection_leftEigenmap f D c φ ψ h₁ h₂ h₃] with q hrange hleft
  intro t
  apply C0Semigroup.comp_comm_of_generator_comm
  intro x y hxy
  obtain ⟨v, hv, hy⟩ := (frontPencilC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ q x y).mp hxy
  rw [frontPencilC0Semigroup_hasGeneratorAt_iff]
  have hPy : frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q y =
      frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q •
        frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q x := by
    rw [← hy, hleft v, hv]
  rw [hPy]
  exact hrange x

/-- Critical scalar evolution on either side of the full semigroup. -/
theorem eventually_frontPencilSemigroup_critical_eq :
    ∀ᶠ q : ℂ in 𝓝 0, ∀ t : NNReal,
      (frontPencilC0Semigroup f D c φ h₁ h₂ q t).comp
          (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q) =
        Complex.exp ((t : ℂ) * frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q) •
          frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q ∧
      (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q).comp
          (frontPencilC0Semigroup f D c φ h₁ h₂ q t) =
        Complex.exp ((t : ℂ) * frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q) •
          frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q := by
  filter_upwards [eventually_frontCriticalProjection_eigenrange f D c φ ψ h₁ h₂ h₃,
    eventually_frontPencilSemigroup_comp_criticalProjection f D c φ ψ h₁ h₂ h₃]
    with q hrange hcomm
  intro t
  have heq := (frontPencilC0Semigroup f D c φ h₁ h₂ q).comp_eq_exp_smul_of_generator_eigenrange
    (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q)
    (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q)
    (fun x ↦ (frontPencilC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ q _ _).mpr (hrange x)) t
  exact ⟨heq, (hcomm t).symm.trans heq⟩

/-- The complementary kernel remains invariant under the longitudinal flow. -/
theorem eventually_frontPencilSemigroup_preserves_criticalKernel :
    ∀ᶠ q : ℂ in 𝓝 0, ∀ (t : NNReal) (x : BUC ℝ (ℂ^n)),
      frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q x = 0 →
        frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q
          (frontPencilC0Semigroup f D c φ h₁ h₂ q t x) = 0 := by
  filter_upwards [eventually_frontPencilSemigroup_comp_criticalProjection f D c φ ψ h₁ h₂ h₃]
    with q hq
  intro t x hx
  have heq := congrArg (fun A : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) ↦ A x) (hq t)
  simpa only [ContinuousLinearMap.comp_apply, hx, map_zero] using! heq.symm

/-- The complementary projection commutes with evolution at small complex contour frequencies. -/
theorem eventually_frontComplexFrequencySemigroup_comp_complement :
    ∀ᶠ ξ : ℂ^m in 𝓝 0, ∀ (ξ₀ ξ₁ : ℝ^m), complexFrequencyShift ξ₀ ξ₁ = ξ →
      ∀ t : NNReal,
        (frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t).comp
            (ContinuousLinearMap.id ℂ (BUC ℝ (ℂ^n)) -
              frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ) =
          (ContinuousLinearMap.id ℂ (BUC ℝ (ℂ^n)) -
              frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ).comp
            (frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t) := by
  filter_upwards [(tendsto_complexFrequencyQuadratic_zero (m := m)).eventually
    (eventually_frontPencilSemigroup_comp_criticalProjection f D c φ ψ h₁ h₂ h₃)] with ξ hξ
  intro ξ₀ ξ₁ hshift t
  rw [frontComplexFrequencyC0Semigroup_eq_pencil, hshift]
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
    frontCriticalProjectionAtComplexFrequency, hξ t]

end

end Planarwave
