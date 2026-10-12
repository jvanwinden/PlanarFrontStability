/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAllFrequencySemigroup
import all Planarwave.Analysis.ComplexFrequencyCriticalSpectrum
import Planarwave.Analysis.SemigroupEigenvector

/-!
# Evolution on the critical spectral subspace

The common-domain eigenvector and spectral projection from Proposition 2.1 are connected to
the semigroup constructed in Lemma 2.2. This proves the exact scalar evolution identity used
in the second part of Lemma 2.3, before applying the Taylor estimates.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The critical projection takes values in the common domain and in the critical eigenspace. -/
theorem eventually_frontCriticalProjection_eigenrange :
    ∀ᶠ q : ℂ in 𝓝 0, ∀ x : BUC ℝ (ℂ^n), ∃ v : ComplexBUC2 (ℂ^n),
      ComplexBUC2.value (ℂ^n) v = frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q x ∧
        frontLongitudinalPencil f D c φ h₁ h₂ q v =
          frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q •
            frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q x := by
  filter_upwards [eventually_frontCriticalEigenvalue_equation f D c φ ψ h₁ h₂ h₃] with q hq
  intro x
  let F := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let a := F.criticalLeftFunctional (diffusionValue (frontComplexifiedDiffusion D)) q x
  let v := frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ q
  have hP : frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q x =
      a • ComplexBUC2.valueCLM (ℂ^n) v := rfl
  refine ⟨a • v, ?_, ?_⟩
  · rw [hP]
    exact (ComplexBUC2.valueCLM (ℂ^n)).map_smul a v
  · rw [map_smul, hP]
    rw [show frontLongitudinalPencil f D c φ h₁ h₂ q v =
      frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q • ComplexBUC2.valueCLM (ℂ^n) v from hq]
    exact smul_comm _ _ _

variable [Nontrivial (ℝ^n)]

/-- At all sufficiently small complex frequencies the semigroup on the critical range is the
scalar exponential of the critical eigenvalue. -/
theorem eventually_frontCriticalSemigroup_eq :
    ∀ᶠ ξ : ℂ^m in 𝓝 0, ∀ (ξ₀ ξ₁ : ℝ^m), complexFrequencyShift ξ₀ ξ₁ = ξ →
      ∀ t : NNReal,
        (frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t).comp
            (frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ) =
          Complex.exp ((t : ℂ) *
              frontCriticalEigenvalueAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ) •
            frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ := by
  filter_upwards [(tendsto_complexFrequencyQuadratic_zero (m := m)).eventually
    (eventually_frontCriticalProjection_eigenrange f D c φ ψ h₁ h₂ h₃)] with ξ hξ
  intro ξ₀ ξ₁ hshift t
  apply C0Semigroup.comp_eq_exp_smul_of_generator_eigenrange
  intro x
  rw [frontComplexFrequencyC0Semigroup_hasGeneratorAt_iff]
  rw [hshift]
  exact hξ x

end

end Planarwave
