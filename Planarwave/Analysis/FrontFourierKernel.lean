/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierSymbol
import Planarwave.Analysis.GaussianFourierKernel

/-!
# The longitudinal-operator-valued remainder kernel

The inner Fourier integral in Section 3 exists in operator norm at every positive
time, for every real spatial displacement and every imaginary contour offset.
We retain the Gaussian frequency mass in its bound. The shifted integral is
defined with the paper's extracted real exponential. Equality between different
contours is proved separately in `FrontFourierContour`; it is not part of the definition.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-- The real-frequency parametrization of a fixed shifted contour is continuous. -/
theorem continuous_complexFrequencyShift_left {m : ℕ} (η : ℝ^m) :
    Continuous (fun ξ : ℝ^m ↦ complexFrequencyShift ξ η) := by
  unfold complexFrequencyShift embed
  fun_prop

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

-- Pin the operator scalar actions to avoid repeated expensive instance searches.
local instance : SMul ℂ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.instSMul

local instance : MulAction ℂ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.mulAction

local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  (SeminormedAddGroup.toESeminormedAddMonoid
    (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))).toContinuousENorm

local instance : NormSMulClass ℂ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) := by
  exact NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))

/-- The shifted remainder symbol, restricted to a real Fourier contour, is norm-continuous. -/
theorem continuous_frontFourierRemainderSymbol_shift (t : NNReal) (η : ℝ^m) :
    Continuous (fun ξ : ℝ^m ↦ frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t
      (complexFrequencyShift ξ η)) :=
  (contDiff_frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t).continuous.comp
    (continuous_complexFrequencyShift_left η)

/-- The paper's inner Fourier integral is absolutely convergent, even in bounded-operator
norm, at every positive time and on every fixed shifted contour. -/
theorem integrable_frontFourierRemainderKernel (t : NNReal) (ht : 0 < t) (η x : ℝ^m) :
    Integrable (fun ξ : ℝ^m ↦ Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) •
      frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (complexFrequencyShift ξ η)) := by
  obtain ⟨M, _, μ, hμ, κ, _, hb⟩ := exists_frontFourierRemainderSymbol_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine integrable_oscillatory_of_gaussian_bound
    (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
    (continuous_frontFourierRemainderSymbol_shift f D c φ h₁ h₂ ψ h₃ t η)
    (b := μ * t) (C := M * Real.exp (κ * t + κ * ‖η‖ ^ 2 * t)) (mul_pos hμ ht) ?_ x
  intro ξ
  apply (hb ξ η t).trans_eq
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- At positive time the unnormalized inverse Fourier integral is norm-continuous
in the displacement, on each fixed shifted contour. -/
theorem continuous_frontFourierRemainderIntegral (t : NNReal) (ht : 0 < t) (η : ℝ^m) :
    Continuous (oscillatoryIntegral (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
      (fun ξ : ℝ^m ↦ frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t
        (complexFrequencyShift ξ η))) := by
  obtain ⟨M, _, μ, hμ, κ, _, hb⟩ := exists_frontFourierRemainderSymbol_bound (m := m) f D c φ h₁ h₂ ψ h₃
  apply continuous_oscillatoryIntegral_of_gaussian_bound
    (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
    (continuous_frontFourierRemainderSymbol_shift f D c φ h₁ h₂ ψ h₃ t η)
    (b := μ * t) (C := M * Real.exp (κ * t + κ * ‖η‖ ^ 2 * t)) (mul_pos hμ ht)
  intro ξ
  apply (hb ξ η t).trans_eq
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The shifted operator-valued kernel, with the real exponential extracted as in (3.5).
The Fourier normalization `(2π)⁻ᵐ` is not included, in agreement with the paper's `H`. -/
def frontShiftedRemainderKernel (t : NNReal) (η x : ℝ^m) : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  Complex.exp (-(⟪η, x⟫_ℝ : ℂ)) • oscillatoryIntegral (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
    (fun ξ : ℝ^m ↦ frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t
      (complexFrequencyShift ξ η)) x

/-- The original real-contour remainder kernel. -/
def frontRemainderKernel (t : NNReal) (x : ℝ^m) : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  frontShiftedRemainderKernel f D c φ h₁ h₂ ψ h₃ t 0 x

/-- The shifted kernel is continuous in the spatial displacement at positive time. -/
theorem continuous_frontShiftedRemainderKernel (t : NNReal) (ht : 0 < t) (η : ℝ^m) :
    Continuous (frontShiftedRemainderKernel f D c φ h₁ h₂ ψ h₃ t η) := by
  have ha : Continuous (fun x : ℝ^m ↦ Complex.exp (-(⟪η, x⟫_ℝ : ℂ))) := by fun_prop
  exact ha.smul
    (continuous_frontFourierRemainderIntegral f D c φ h₁ h₂ ψ h₃ t ht η)

/-- The original real-contour kernel is continuous in operator norm. -/
theorem continuous_frontRemainderKernel (t : NNReal) (ht : 0 < t) :
    Continuous (frontRemainderKernel (m := m) f D c φ h₁ h₂ ψ h₃ t) :=
  continuous_frontShiftedRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht 0

/-- At zero shift this is exactly the inner integral in the definition of `H`. -/
theorem frontRemainderKernel_eq_integral (t : NNReal) (x : ℝ^m) :
    frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x =
      ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) •
        frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (embed ξ) := by
  have hzero : (embed (0 : ℝ^m) : ℂ^m) = 0 := by ext i; simp [embed]
  simp [frontRemainderKernel, frontShiftedRemainderKernel, oscillatoryIntegral,
    complexFrequencyShift, hzero]

/-- Applying the operator kernel to a longitudinal slice agrees with the paper's
Banach-valued integral. No interchange of conditionally convergent integrals is used. -/
theorem frontRemainderKernel_apply (t : NNReal) (ht : 0 < t) (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x v =
      ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) •
        (frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (embed ξ) v) := by
  have hzero : (embed (0 : ℝ^m) : ℂ^m) = 0 := by ext i; simp [embed]
  have hint := integrable_frontFourierRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht 0 x
  simp only [complexFrequencyShift, hzero, smul_zero, add_zero] at hint
  rw [frontRemainderKernel_eq_integral]
  simpa only [smul_apply] using!
    ContinuousLinearMap.integral_apply hint v

/-- Evaluation in the longitudinal coordinate also commutes with the integral,
giving the pointwise kernel appearing in (3.4). -/
theorem frontRemainderKernel_apply_apply (t : NNReal) (ht : 0 < t) (x : ℝ^m)
    (v : BUC ℝ (ℂ^n)) (z : ℝ) :
    frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x v z =
      ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) •
        (frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (embed ξ) v z) := by
  have hzero : (embed (0 : ℝ^m) : ℂ^m) = 0 := by ext i; simp [embed]
  have hint := integrable_frontFourierRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht 0 x
  simp only [complexFrequencyShift, hzero, smul_zero, add_zero] at hint
  let L : (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) →L[ℂ] ℂ^n :=
    (BUC.evalCLM (𝕜 := ℂ) z).comp (ContinuousLinearMap.apply ℂ (BUC ℝ (ℂ^n)) v)
  rw [frontRemainderKernel_eq_integral]
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    smul_apply, BUC.evalCLM_apply, BUC.smul_apply] using!
    (ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ)
      (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) (Fₗ := ℂ^n) L hint).symm

/-- Integrating the all-frequency estimate gives the basic shifted-kernel bound.
This is the first estimate in the proof of the off-diagonal proposition. -/
theorem exists_frontShiftedRemainderKernel_gaussian_bound :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (t : NNReal), 0 < t → ∀ η x : ℝ^m,
      ‖frontShiftedRemainderKernel f D c φ h₁ h₂ ψ h₃ t η x‖ ≤
        M * (Real.pi / (μ * t)) ^ (m / 2 : ℝ) *
          Real.exp (κ * t - ⟪η, x⟫_ℝ + κ * ‖η‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, hb⟩ := exists_frontFourierRemainderSymbol_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨M, hM, μ, hμ, κ, hκ, ?_⟩
  intro t ht η x
  have hfreq : ∀ ξ : ℝ^m,
      ‖frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (complexFrequencyShift ξ η)‖ ≤
        (M * Real.exp (κ * t + κ * ‖η‖ ^ 2 * t)) * Real.exp (-(μ * t) * ‖ξ‖ ^ 2) := by
    intro ξ
    apply (hb ξ η t).trans_eq
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h := norm_oscillatoryIntegral_le_gaussian
    (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
    (continuous_frontFourierRemainderSymbol_shift f D c φ h₁ h₂ ψ h₃ t η)
    (mul_pos hμ ht) hfreq x
  rw [frontShiftedRemainderKernel]
  have hn (a : ℂ) (A : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) : ‖a • A‖ = ‖a‖ * ‖A‖ :=
    norm_smul a A
  rw [hn, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
  rw [finrank_euclideanSpace_fin]
  calc
    Real.exp (-⟪η, x⟫_ℝ) *
        (M * Real.exp (κ * t + κ * ‖η‖ ^ 2 * t) * (Real.pi / (μ * t)) ^ (m / 2 : ℝ)) =
        M * (Real.pi / (μ * t)) ^ (m / 2 : ℝ) *
          (Real.exp (-⟪η, x⟫_ℝ) * Real.exp (κ * t + κ * ‖η‖ ^ 2 * t)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end

end Planarwave
