/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontCompactSemigroupBounds
import Planarwave.Analysis.SemigroupParameterAnalytic

/-!
# The holomorphic Fourier symbol of the spatial remainder

Section 3 defines the remainder symbol as the longitudinal semigroup minus the
transverse heat multiplier times the zero-frequency projection. The parameter
analyticity proved here is in operator norm on the entire complex frequency space;
time analyticity alone would not justify the paper's frequency contour shift.
-/

open scoped ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- At fixed time the full longitudinal semigroup is entire in the analytic pencil parameter. -/
theorem contDiff_frontPencilSemigroup_parameter (t : NNReal) :
    ContDiff ℂ ω (fun q : ℂ ↦ frontPencilC0Semigroup f D c φ h₁ h₂ q t) := by
  exact ((frontLinearizedC0Semigroup f D c φ h₁ h₂ 0).contDiff_boundedPerturbation_coefficient t).comp
    (contDiff_neg.smul contDiff_const)

/-- The operator-valued Fourier symbol before subtracting the critical heat evolution. -/
def frontFourierSemigroupSymbol (t : NNReal) (ξ : ℂ^m) : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  frontPencilC0Semigroup f D c φ h₁ h₂ (complexFrequencyQuadratic ξ) t

/-- Agreement with the previously constructed semigroup on every shifted real contour. -/
theorem frontFourierSemigroupSymbol_shift (t : NNReal) (ξ₀ ξ₁ : ℝ^m) :
    frontFourierSemigroupSymbol f D c φ h₁ h₂ t (complexFrequencyShift ξ₀ ξ₁) =
      frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t := by
  rw [frontComplexFrequencyC0Semigroup_eq_pencil]
  rfl

/-- Entire operator-norm dependence on the complex transverse Fourier vector. -/
theorem contDiff_frontFourierSemigroupSymbol (t : NNReal) :
    ContDiff ℂ ω (frontFourierSemigroupSymbol (m := m) f D c φ h₁ h₂ t) :=
  (contDiff_frontPencilSemigroup_parameter f D c φ h₁ h₂ t).comp contDiff_complexFrequencyQuadratic

variable (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The symbol `Ŝξ(t)` in the paper's definition of the remainder kernel `H`. -/
def frontFourierRemainderSymbol (t : NNReal) (ξ : ℂ^m) : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  frontFourierSemigroupSymbol f D c φ h₁ h₂ t ξ -
    Complex.exp (-(t * d_perp D φ ψ : ℂ) * complexFrequencyQuadratic ξ) •
      profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)

/-- The remainder symbol is entire, as needed to shift the Fourier contour. -/
theorem contDiff_frontFourierRemainderSymbol (t : NNReal) :
    ContDiff ℂ ω (frontFourierRemainderSymbol (m := m) f D c φ h₁ h₂ ψ h₃ t) := by
  unfold frontFourierRemainderSymbol
  apply (contDiff_frontFourierSemigroupSymbol f D c φ h₁ h₂ t).sub
  have hq : ContDiff ℂ ω (fun ξ : ℂ^m ↦
      -(t * d_perp D φ ψ : ℂ) * complexFrequencyQuadratic ξ) :=
    contDiff_const.mul contDiff_complexFrequencyQuadratic
  let A : ℂ →L[ℂ] (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight
      (profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃))
  exact (ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := ℂ)
    (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) A).comp hq.cexp

/-- Lemma 2.2 also controls the remainder symbol, including the norm of the fixed
critical projection in the prefactor. -/
theorem exists_frontFourierRemainderSymbol_bound :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal),
      ‖frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (complexFrequencyShift ξ₀ ξ₁)‖ ≤
        M * Real.exp (κ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, hb⟩ := exists_front_allFrequency_bound (m := m) f D c φ h₁ h₂ ψ h₃
  let P := profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  refine ⟨M * (‖P‖ + 1), by positivity, μ, hμ, κ, hκ, ?_⟩
  intro ξ₀ ξ₁ t
  let S := frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t
  let a := Complex.exp (-(t * d_perp D φ ψ : ℂ) * complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))
  rw [frontFourierRemainderSymbol, frontFourierSemigroupSymbol_shift]
  calc
    ‖S - a • P‖ ≤ ‖S‖ + ‖a‖ * ‖P‖ := (norm_sub_le _ _).trans_eq (by rw [norm_smul])
    _ ≤ (‖S‖ + ‖a‖) * (‖P‖ + 1) := by
      nlinarith [norm_nonneg S, norm_nonneg a, norm_nonneg P, mul_nonneg (norm_nonneg S) (norm_nonneg P)]
    _ ≤ (M * Real.exp (κ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t)) * (‖P‖ + 1) :=
      mul_le_mul_of_nonneg_right (hb ξ₀ ξ₁ t) (by positivity)
    _ = _ := by ring

end

end Planarwave
