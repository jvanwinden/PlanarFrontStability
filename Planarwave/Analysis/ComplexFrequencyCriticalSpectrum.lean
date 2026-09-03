/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Planarwave.Analysis.FrontEigenvalueBranch

/-!
# The critical spectrum at multidimensional complex frequency

Proposition 2.1 is stated for a complex transverse frequency vector `ξ`.  The longitudinal
operator depends on that vector only through the holomorphic quadratic form

`λ₀(ξ) = ∑ i, ξᵢ²`.

This file composes the scalar analytic-parameter construction with that quadratic form.  It
thereby recovers the paper's multidimensional holomorphic eigenvalue and projection, their
`O(‖ξ‖⁴)` and `O(‖ξ‖²)` bounds, and the bounded-window spectral separation.
-/

open Filter Function
open Asymptotics
open scoped BigOperators Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" m:arg => EuclideanSpace ℝ (Fin m)
local notation "ℂ^" m:arg => EuclideanSpace ℂ (Fin m)

section FrequencyQuadratic

variable {m : ℕ}

/-- The holomorphic quadratic form `λ₀(ξ)=∑ᵢ ξᵢ²` from Section 2 of the paper.  It is not a
Hermitian norm square when `ξ` is complex. -/
def complexFrequencyQuadratic (ξ : ℂ^m) : ℂ :=
  ∑ i, (ξ i) ^ 2

@[simp]
theorem complexFrequencyQuadratic_zero :
    complexFrequencyQuadratic (0 : ℂ^m) = 0 := by
  simp [complexFrequencyQuadratic]

/-- The frequency quadratic is entire. -/
theorem contDiff_complexFrequencyQuadratic :
    ContDiff ℂ ⊤ (complexFrequencyQuadratic : ℂ^m → ℂ) := by
  unfold complexFrequencyQuadratic
  fun_prop

/-- The frequency quadratic tends to zero with the frequency. -/
theorem tendsto_complexFrequencyQuadratic_zero :
    Tendsto (complexFrequencyQuadratic : ℂ^m → ℂ) (𝓝 0) (𝓝 0) := by
  have hcontinuous :
      ContinuousAt (complexFrequencyQuadratic : ℂ^m → ℂ) 0 :=
    (contDiff_complexFrequencyQuadratic (m := m)).continuous.continuousAt
  change Tendsto (complexFrequencyQuadratic : ℂ^m → ℂ) (𝓝 0)
    (𝓝 (complexFrequencyQuadratic (0 : ℂ^m))) at hcontinuous
  rw [complexFrequencyQuadratic_zero] at hcontinuous
  exact hcontinuous

/-- Although `λ₀` is not positive on complex frequencies, its modulus is bounded by the squared
Euclidean norm. -/
theorem norm_complexFrequencyQuadratic_le (ξ : ℂ^m) :
    ‖complexFrequencyQuadratic ξ‖ ≤ ‖ξ‖ ^ 2 := by
  calc
    ‖complexFrequencyQuadratic ξ‖ = ‖∑ i, (ξ i) ^ 2‖ := rfl
    _ ≤ ∑ i, ‖(ξ i) ^ 2‖ := norm_sum_le _ _
    _ = ∑ i, ‖ξ i‖ ^ 2 := by simp only [norm_pow]
    _ = ‖ξ‖ ^ 2 := (EuclideanSpace.norm_sq_eq ξ).symm

/-- On an embedded real frequency, the holomorphic quadratic form is the usual squared
Euclidean norm. -/
theorem complexFrequencyQuadratic_embed (ξ : ℝ^m) :
    complexFrequencyQuadratic (embed ξ) = (‖ξ‖ ^ 2 : ℂ) := by
  change ∑ i, ((ξ i : ℂ) ^ 2) = (‖ξ‖ ^ 2 : ℂ)
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  push_cast
  rfl

end FrequencyQuadratic

section FrontCriticalFrequency

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n)
  (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The critical eigenvalue at a multidimensional complex transverse frequency. -/
def frontCriticalEigenvalueAtComplexFrequency (ξ : ℂ^m) : ℂ :=
  frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ (complexFrequencyQuadratic ξ)

/-- The critical spectral projection at a multidimensional complex transverse frequency. -/
def frontCriticalProjectionAtComplexFrequency (ξ : ℂ^m) :
    BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  frontCriticalProjection f D c φ ψ h₁ h₂ h₃ (complexFrequencyQuadratic ξ)

@[simp]
theorem frontCriticalEigenvalueAtComplexFrequency_zero :
    frontCriticalEigenvalueAtComplexFrequency (m := m) f D c φ ψ h₁ h₂ h₃ 0 = 0 := by
  simp [frontCriticalEigenvalueAtComplexFrequency]

@[simp]
theorem frontCriticalProjectionAtComplexFrequency_zero :
    frontCriticalProjectionAtComplexFrequency (m := m) f D c φ ψ h₁ h₂ h₃ 0 =
      profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) := by
  simp [frontCriticalProjectionAtComplexFrequency]

/-- Holomorphic dependence of the critical eigenvalue on the complex frequency vector. -/
theorem contDiffAt_frontCriticalEigenvalueAtComplexFrequency :
    ContDiffAt ℂ ⊤
      (frontCriticalEigenvalueAtComplexFrequency (m := m) f D c φ ψ h₁ h₂ h₃) 0 := by
  have hq : ContDiffAt ℂ ⊤ (complexFrequencyQuadratic : ℂ^m → ℂ) 0 :=
    (contDiff_complexFrequencyQuadratic (m := m)).contDiffAt
  have houter : ContDiffAt ℂ ⊤
      (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃)
      (complexFrequencyQuadratic (0 : ℂ^m)) := by
    simpa using contDiffAt_frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃
  exact houter.comp (0 : ℂ^m) hq

/-- Holomorphic dependence of the critical spectral projection on the complex frequency vector. -/
theorem contDiffAt_frontCriticalProjectionAtComplexFrequency :
    ContDiffAt ℂ ⊤
      (frontCriticalProjectionAtComplexFrequency (m := m) f D c φ ψ h₁ h₂ h₃) 0 := by
  have hq : ContDiffAt ℂ ⊤ (complexFrequencyQuadratic : ℂ^m → ℂ) 0 :=
    (contDiff_complexFrequencyQuadratic (m := m)).contDiffAt
  have houter : ContDiffAt ℂ ⊤
      (frontCriticalProjection f D c φ ψ h₁ h₂ h₃)
      (complexFrequencyQuadratic (0 : ℂ^m)) := by
    simpa using contDiffAt_frontCriticalProjection f D c φ ψ h₁ h₂ h₃
  exact houter.comp (0 : ℂ^m) hq

/-- The multidimensional form of Proposition 2.1(3): one positive constant controls both the
fourth-order eigenvalue remainder and the second-order projection remainder. -/
theorem exists_frontCriticalExpansion_complexFrequency_bound :
    ∃ C₀ > 0, ∀ᶠ ξ : ℂ^m in 𝓝 0,
      ‖frontCriticalEigenvalueAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ +
          (d_perp D φ ψ : ℂ) * complexFrequencyQuadratic ξ‖ ≤ C₀ * ‖ξ‖ ^ 4 ∧
        ‖frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ -
          profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)‖ ≤
            C₀ * ‖ξ‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    exists_frontCriticalExpansion_bound f D c φ ψ h₁ h₂ h₃
  have hquadratic := tendsto_complexFrequencyQuadratic_zero (m := m)
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hquadratic.eventually hbound] with ξ hξ
  have hq := norm_complexFrequencyQuadratic_le ξ
  rcases hξ with ⟨heig, hproj⟩
  constructor
  · calc
      ‖frontCriticalEigenvalueAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ +
          (d_perp D φ ψ : ℂ) * complexFrequencyQuadratic ξ‖ =
          ‖frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃
              (complexFrequencyQuadratic ξ) +
            complexFrequencyQuadratic ξ * (d_perp D φ ψ : ℂ)‖ := by
              simp [frontCriticalEigenvalueAtComplexFrequency, mul_comm]
      _ ≤ C₀ * ‖complexFrequencyQuadratic ξ‖ ^ 2 := heig
      _ ≤ C₀ * (‖ξ‖ ^ 2) ^ 2 := by
        gcongr
      _ = C₀ * ‖ξ‖ ^ 4 := by ring
  · calc
      ‖frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ -
          profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)‖ =
          ‖frontCriticalProjection f D c φ ψ h₁ h₂ h₃
              (complexFrequencyQuadratic ξ) -
            profileProjection ψ h₃.integrable
              (translationModeBUC f D c φ ψ h₃)‖ := rfl
      _ ≤ C₀ * ‖complexFrequencyQuadratic ξ‖ := hproj
      _ ≤ C₀ * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_left hq hC₀.le

/-- Bounded-window form of Proposition 2.1(1) for multidimensional complex frequencies.  In the
right spectral half-plane, the only possible spectrum in a fixed disk is the critical branch. -/
theorem exists_eventually_frontComplexFrequencyPencil_not_bijective_iff_branch_on_bounded_gap :
    ∃ θ > 0, ∀ R : ℝ,
      ∀ᶠ ξ : ℂ^m in 𝓝 0, ∀ z : ℂ,
        ‖z‖ ≤ R → -(θ / 2) ≤ z.re →
          (¬ Function.Bijective
              (frontLongitudinalPencil f D c φ h₁ h₂
                  (complexFrequencyQuadratic ξ) -
                z • ComplexBUC2.valueCLM (ℂ^n)) ↔
            z = frontCriticalEigenvalueAtComplexFrequency
              f D c φ ψ h₁ h₂ h₃ ξ) := by
  obtain ⟨θ, hθ, hwindow⟩ :=
    exists_eventually_frontLongitudinalPencil_not_bijective_iff_branch_on_bounded_gap
      f D c φ ψ h₁ h₂ h₃
  refine ⟨θ, hθ, ?_⟩
  intro R
  filter_upwards [
    (tendsto_complexFrequencyQuadratic_zero (m := m)).eventually (hwindow R)] with ξ hξ
  simpa [frontCriticalEigenvalueAtComplexFrequency] using hξ

/-- Near zero complex frequency, the critical projection is rank one and its kernel is the range
of the longitudinal pencil shifted by the critical eigenvalue. -/
theorem eventually_frontCriticalProjectionAtComplexFrequency_spectralSplitting :
    ∀ᶠ ξ : ℂ^m in 𝓝 0,
      Module.finrank ℂ
          (LinearMap.range
            (frontCriticalProjectionAtComplexFrequency
              f D c φ ψ h₁ h₂ h₃ ξ).toLinearMap) = 1 ∧
        LinearMap.ker
            (frontCriticalProjectionAtComplexFrequency
              f D c φ ψ h₁ h₂ h₃ ξ).toLinearMap =
          LinearMap.range
            (frontCriticalShiftedPencil f D c φ ψ h₁ h₂ h₃
              (complexFrequencyQuadratic ξ)).toLinearMap := by
  exact (tendsto_complexFrequencyQuadratic_zero (m := m)).eventually
    (eventually_frontCriticalProjection_spectralSplitting f D c φ ψ h₁ h₂ h₃)

end FrontCriticalFrequency

end

end Planarwave
