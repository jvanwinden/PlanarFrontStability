/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Planarwave.Analysis.ComplexFrequencyCriticalSpectrum
import Planarwave.Analysis.ConvectiveHeatSemigroup

/-!
# Complex-frequency bounds used in the longitudinal semigroup estimates

This file begins the formalization of Lemma 2.2 in the cited paper.  It first proves the
"elementary" scalar exponential estimate separated off at the start of the paper's proof.  The
calculation is based on the exact identity

`Re λ₀(ξ₀ + i ξ₁) = ‖ξ₀‖² - ‖ξ₁‖²`.

`FrontAllFrequencySemigroup` completes the operator-semigroup part of Lemma 2.2 by applying
the bounded-perturbation theorem twice and using the contour-shift estimates proved here.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" m:arg => EuclideanSpace ℝ (Fin m)
local notation "ℂ^" m:arg => EuclideanSpace ℂ (Fin m)

section FrequencyShift

variable {m : ℕ}

/-- The paper's complex contour frequency `ξ₀ + i ξ₁`, with real and imaginary parts represented
as real Euclidean vectors. -/
def complexFrequencyShift (ξ₀ ξ₁ : ℝ^m) : ℂ^m :=
  embed ξ₀ + Complex.I • embed ξ₁

@[simp]
theorem complexFrequencyShift_apply (ξ₀ ξ₁ : ℝ^m) (i : Fin m) :
    complexFrequencyShift ξ₀ ξ₁ i = (ξ₀ i : ℂ) + Complex.I * (ξ₁ i : ℂ) := by
  simp [complexFrequencyShift, embed]

/-- Real part of the holomorphic transverse quadratic form on the shifted contour. -/
theorem complexFrequencyQuadratic_shift_re (ξ₀ ξ₁ : ℝ^m) :
    (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)).re =
      ‖ξ₀‖ ^ 2 - ‖ξ₁‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [complexFrequencyQuadratic, complexFrequencyShift, pow_two, embed]

/-- Imaginary part of the holomorphic transverse quadratic form on the shifted contour. -/
theorem complexFrequencyQuadratic_shift_im (ξ₀ ξ₁ : ℝ^m) :
    (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)).im =
      2 * ⟪ξ₀, ξ₁⟫_ℝ := by
  simp [complexFrequencyQuadratic, complexFrequencyShift, pow_two, embed,
    PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Quantitative change of `λ₀` under the imaginary contour shift.  This is the scalar algebra
behind the first inequality in (2.4). -/
theorem norm_complexFrequencyQuadratic_shift_sub_le (ξ₀ ξ₁ : ℝ^m) :
    ‖complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁) -
        ((‖ξ₀‖ ^ 2 : ℝ) : ℂ)‖ ≤
      ‖ξ₁‖ ^ 2 + 2 * (‖ξ₀‖ * ‖ξ₁‖) := by
  let z := complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁) -
    ((‖ξ₀‖ ^ 2 : ℝ) : ℂ)
  have hinner : |⟪ξ₀, ξ₁⟫_ℝ| ≤ ‖ξ₀‖ * ‖ξ₁‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) ξ₀ ξ₁
  have hzre : z.re = -(‖ξ₁‖ ^ 2) := by
    change (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)).re -
      ‖ξ₀‖ ^ 2 = -(‖ξ₁‖ ^ 2)
    rw [complexFrequencyQuadratic_shift_re]
    ring
  have hzim : z.im = 2 * ⟪ξ₀, ξ₁⟫_ℝ := by
    change (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)).im - 0 =
      2 * ⟪ξ₀, ξ₁⟫_ℝ
    rw [complexFrequencyQuadratic_shift_im]
    ring
  calc
    ‖complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁) -
        ((‖ξ₀‖ ^ 2 : ℝ) : ℂ)‖ = ‖z‖ := rfl
    _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ = ‖ξ₁‖ ^ 2 + 2 * |⟪ξ₀, ξ₁⟫_ℝ| := by
      rw [hzre, hzim, abs_neg, abs_of_nonneg (sq_nonneg ‖ξ₁‖), abs_mul]
      norm_num
    _ ≤ ‖ξ₁‖ ^ 2 + 2 * (‖ξ₀‖ * ‖ξ₁‖) := by gcongr

/-- Young's inequality puts the contour-shift change in the precise quadratic form used in
(2.4). -/
theorem norm_complexFrequencyQuadratic_shift_sub_le_young
    (ξ₀ ξ₁ : ℝ^m) {δ : ℝ} (hδ : 0 < δ) :
    ‖complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁) -
        ((‖ξ₀‖ ^ 2 : ℝ) : ℂ)‖ ≤
      δ * ‖ξ₀‖ ^ 2 + (1 + δ⁻¹) * ‖ξ₁‖ ^ 2 := by
  calc
    ‖complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁) -
        ((‖ξ₀‖ ^ 2 : ℝ) : ℂ)‖ ≤
        ‖ξ₁‖ ^ 2 + 2 * (‖ξ₀‖ * ‖ξ₁‖) :=
      norm_complexFrequencyQuadratic_shift_sub_le ξ₀ ξ₁
    _ ≤ ‖ξ₁‖ ^ 2 +
        (δ * ‖ξ₀‖ ^ 2 + δ⁻¹ * ‖ξ₁‖ ^ 2) := by
      gcongr
      simpa [mul_assoc] using two_mul_le_add_mul_sq (a := ‖ξ₀‖) (b := ‖ξ₁‖) hδ
    _ = δ * ‖ξ₀‖ ^ 2 + (1 + δ⁻¹) * ‖ξ₁‖ ^ 2 := by ring

/-- Exact modulus of the scalar heat multiplier at a complex contour frequency. -/
theorem norm_exp_neg_mul_complexFrequencyQuadratic_shift
    (d t : ℝ) (ξ₀ ξ₁ : ℝ^m) :
    ‖Complex.exp
        (-(t * d : ℂ) * complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ =
      Real.exp (-t * d * (‖ξ₀‖ ^ 2 - ‖ξ₁‖ ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.mul_re]
  simp [complexFrequencyQuadratic_shift_re]

/-- The scalar heat multiplier satisfies the all-frequency estimate from Lemma 2.2 with
prefactor one.  The harmless `exp (d t)` term is retained to match the common form used for the
operator semigroup in the paper. -/
theorem exists_heatMultiplier_allFrequency_bound {d : ℝ} (hd : 0 < d) :
    ∃ μ > 0, ∃ κ > 0, ∀ (t : ℝ) (ξ₀ ξ₁ : ℝ^m), 0 ≤ t →
      ‖Complex.exp
          (-(t * d : ℂ) * complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ ≤
        Real.exp (κ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  refine ⟨d, hd, d, hd, ?_⟩
  intro t ξ₀ ξ₁ ht
  rw [norm_exp_neg_mul_complexFrequencyQuadratic_shift]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hd.le ht]

end FrequencyShift

section FrontFrequencyPerturbation

variable {m n : ℕ}

/-- Pointwise diffusion on the longitudinal `BUC` state space. -/
def frontComplexifiedDiffusionBUC (D : ℝ^n →L[ℝ] ℝ^n) :
    BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  BUC.postcompCLM (frontComplexifiedDiffusion D)

/-- The bounded operator on the longitudinal state space whose restriction to the common domain
is `L̂_(ξ₀+iξ₁) - L̂_ξ₀`.  Isolating it on `BUC` is what permits the bounded perturbation theorem
in the paper's proof of Lemma 2.2. -/
def frontComplexFrequencyBoundedPerturbation
    (D : ℝ^n →L[ℝ] ℝ^n) (ξ₀ ξ₁ : ℝ^m) :
    BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  (((‖ξ₀‖ ^ 2 : ℝ) : ℂ) -
      complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)) •
    frontComplexifiedDiffusionBUC D

/-- Exact common-domain identity for the bounded contour-shift perturbation. -/
theorem frontLongitudinalPencil_shift_sub_real_eq
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ : ℝ → ℝ^n)
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
    (ξ₀ ξ₁ : ℝ^m) :
    frontLongitudinalPencil f D c φ h₁ h₂
          (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)) -
        frontLongitudinalPencil f D c φ h₁ h₂ (((‖ξ₀‖ ^ 2 : ℝ) : ℂ)) =
      (frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁).comp
        (ComplexBUC2.valueCLM (ℂ^n)) := by
  change longitudinalOperator _ _ _ _ - longitudinalOperator _ _ _ _ = _
  rw [longitudinalOperator_sub]
  ext v z
  rfl

/-- Young-inequality form of (2.4), with the fixed diffusion multiplier displayed explicitly. -/
theorem norm_frontComplexFrequencyBoundedPerturbation_le_young
    (D : ℝ^n →L[ℝ] ℝ^n) (ξ₀ ξ₁ : ℝ^m) {δ : ℝ} (hδ : 0 < δ) :
    ‖frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁‖ ≤
      (δ * ‖ξ₀‖ ^ 2 + (1 + δ⁻¹) * ‖ξ₁‖ ^ 2) *
        ‖frontComplexifiedDiffusionBUC D‖ := by
  calc
    ‖frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁‖ ≤
          ‖(((‖ξ₀‖ ^ 2 : ℝ) : ℂ) -
            complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ *
          ‖frontComplexifiedDiffusionBUC D‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = ‖complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁) -
            (((‖ξ₀‖ ^ 2 : ℝ) : ℂ))‖ *
          ‖frontComplexifiedDiffusionBUC D‖ := by
      rw [norm_sub_rev]
    _ ≤ (δ * ‖ξ₀‖ ^ 2 + (1 + δ⁻¹) * ‖ξ₁‖ ^ 2) *
          ‖frontComplexifiedDiffusionBUC D‖ := by
      gcongr
      exact norm_complexFrequencyQuadratic_shift_sub_le_young ξ₀ ξ₁ hδ

/-- The scalar half of Lemma 2.2 specialized to the positive transverse diffusion coefficient
selected by the front. -/
theorem exists_frontHeatMultiplier_allFrequency_bound
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
    (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    ∃ μ > 0, ∃ κ > 0, ∀ (t : ℝ) (ξ₀ ξ₁ : ℝ^m), 0 ≤ t →
      ‖Complex.exp
          (-(t * d_perp D φ ψ : ℂ) *
            complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ ≤
        Real.exp (κ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) :=
  exists_heatMultiplier_allFrequency_bound
    (frontTransverseDiffusion_pos f D c φ ψ h₃)

end FrontFrequencyPerturbation

end

end Planarwave
