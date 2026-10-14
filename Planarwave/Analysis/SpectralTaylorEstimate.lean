/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

/-!
# Estimates for the critical semigroup Taylor remainder

The estimates here follow the second half of Lemma 2.3: factor out the heat multiplier,
bound the exponential remainder by `|w| exp |w|`, and absorb the polynomial in time and
frequency into a slightly weaker Gaussian.
-/

namespace Planarwave

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The exponential difference estimate after factoring out the reference heat multiplier. -/
theorem norm_exp_smul_sub_exp_smul_le (P P₀ : E) (z w : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp ((t : ℂ) * z) • P - Complex.exp ((t : ℂ) * w) • P₀‖ ≤
      (t * ‖z - w‖ * ‖P‖ + ‖P - P₀‖) * Real.exp (t * w.re + t * ‖z - w‖) := by
  have hfactor : Complex.exp ((t : ℂ) * z) • P - Complex.exp ((t : ℂ) * w) • P₀ =
      Complex.exp ((t : ℂ) * w) •
        ((Complex.exp ((t : ℂ) * (z - w)) - 1) • P + (P - P₀)) := by
    rw [smul_add, smul_sub, sub_smul, one_smul, smul_sub, smul_smul, ← Complex.exp_add]
    rw [show (t : ℂ) * w + (t : ℂ) * (z - w) = (t : ℂ) * z by ring]
    abel
  have hnorm : ‖(t : ℂ) * (z - w)‖ = t * ‖z - w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
  have hexp : ‖Complex.exp ((t : ℂ) * (z - w)) - 1‖ ≤
      t * ‖z - w‖ * Real.exp (t * ‖z - w‖) := by
    simpa [hnorm, abs_of_nonneg ht] using
      Complex.norm_exp_sub_sum_le_norm_mul_exp ((t : ℂ) * (z - w)) 1
  have hheat : ‖Complex.exp ((t : ℂ) * w)‖ = Real.exp (t * w.re) := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hone : 1 ≤ Real.exp (t * ‖z - w‖) := Real.one_le_exp_iff.mpr (by positivity)
  rw [hfactor, norm_smul, hheat]
  calc
    Real.exp (t * w.re) * ‖(Complex.exp ((t : ℂ) * (z - w)) - 1) • P + (P - P₀)‖ ≤
        Real.exp (t * w.re) *
          (‖Complex.exp ((t : ℂ) * (z - w)) - 1‖ * ‖P‖ + ‖P - P₀‖) := by
      gcongr
      simpa only [norm_smul] using norm_add_le
        ((Complex.exp ((t : ℂ) * (z - w)) - 1) • P) (P - P₀)
    _ ≤ Real.exp (t * w.re) *
        ((t * ‖z - w‖ * Real.exp (t * ‖z - w‖)) * ‖P‖ +
          ‖P - P₀‖ * Real.exp (t * ‖z - w‖)) := by
      gcongr
      exact le_mul_of_one_le_right (norm_nonneg _) hone
    _ = _ := by rw [Real.exp_add]; ring

/-- The fourth-order eigenvalue and second-order projection errors yield the paper's
`(ρ² + t ρ⁴)` prefactor. -/
theorem norm_exp_smul_sub_exp_smul_le_taylor (P P₀ : E) (z w : ℂ)
    {t ρ C K : ℝ} (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hz : ‖z - w‖ ≤ C * ρ ^ 4) (hP : ‖P‖ ≤ K) (hP₀ : ‖P - P₀‖ ≤ C * ρ ^ 2) :
    ‖Complex.exp ((t : ℂ) * z) • P - Complex.exp ((t : ℂ) * w) • P₀‖ ≤
      C * (K + 1) * (ρ ^ 2 + t * ρ ^ 4) * Real.exp (t * w.re + C * ρ ^ 4 * t) := by
  apply (norm_exp_smul_sub_exp_smul_le P P₀ z w ht).trans
  have hcoeff : t * ‖z - w‖ * ‖P‖ + ‖P - P₀‖ ≤ C * (K + 1) * (ρ ^ 2 + t * ρ ^ 4) := by
    calc
      t * ‖z - w‖ * ‖P‖ + ‖P - P₀‖ ≤ t * (C * ρ ^ 4) * K + C * ρ ^ 2 := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC hK) (sq_nonneg ρ),
        mul_nonneg (mul_nonneg ht hC) (pow_nonneg hρ 4)]
  apply mul_le_mul hcoeff _ (Real.exp_pos _).le (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hz ht]

/-- A quadratic polynomial is bounded by any positive exponential, with an explicit constant. -/
theorem add_sq_le_exp_mul {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x + x ^ 2 ≤ (a⁻¹ + 2 * (a⁻¹) ^ 2) * Real.exp (a * x) := by
  have h₁ : a * x ≤ Real.exp (a * x) := by
    simpa using Real.pow_div_factorial_le_exp (a * x) (mul_nonneg ha.le hx) 1
  have h₂ : (a * x) ^ 2 / 2 ≤ Real.exp (a * x) := by
    simpa using Real.pow_div_factorial_le_exp (a * x) (mul_nonneg ha.le hx) 2
  have h₁' := mul_le_mul_of_nonneg_left h₁ (inv_nonneg.mpr ha.le)
  have h₂' := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2 * (a⁻¹) ^ 2 by positivity)
  have he₁ : a⁻¹ * (a * x) = x := by field_simp
  have he₂ : (2 * (a⁻¹) ^ 2) * ((a * x) ^ 2 / 2) = x ^ 2 := by field_simp
  rw [he₁] at h₁'
  rw [he₂] at h₂'
  nlinarith

/-- The polynomial Taylor prefactor is absorbed into the Gaussian, as in Lemma 2.3.
Here `a` and `b` are the squared real and imaginary frequencies. -/
theorem polynomial_gaussian_absorption {d C a b t : ℝ} (hd : 0 < d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hsmall : C * (a + b) ≤ d / 2) :
    (a + b + t * (a + b) ^ 2) * Real.exp (-d * a * t + d * b * t + C * (a + b) ^ 2 * t) ≤
      (((d / 4)⁻¹ + 2 * ((d / 4)⁻¹) ^ 2) / t) *
        Real.exp (-(d / 4) * a * t + 2 * d * b * t) := by
  let L := (d / 4)⁻¹ + 2 * ((d / 4)⁻¹) ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hpoly := add_sq_le_exp_mul (show 0 < d / 4 by positivity)
    (show 0 ≤ t * (a + b) by positivity)
  have hrem : C * (a + b) ^ 2 * t ≤ d / 2 * (a + b) * t := by
    have h := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ (a + b) * t by positivity)
    nlinarith
  have hexp : -d * a * t + d * b * t + C * (a + b) ^ 2 * t ≤
      -(d / 2) * a * t + (3 * d / 2) * b * t := by nlinarith
  calc
    (a + b + t * (a + b) ^ 2) * Real.exp (-d * a * t + d * b * t + C * (a + b) ^ 2 * t) ≤
        (a + b + t * (a + b) ^ 2) * Real.exp (-(d / 2) * a * t + (3 * d / 2) * b * t) := by
      gcongr
    _ = t⁻¹ * (t * (a + b) + (t * (a + b)) ^ 2) *
        Real.exp (-(d / 2) * a * t + (3 * d / 2) * b * t) := by field_simp
    _ ≤ t⁻¹ * (L * Real.exp ((d / 4) * (t * (a + b)))) *
        Real.exp (-(d / 2) * a * t + (3 * d / 2) * b * t) := by
      gcongr
    _ = (L / t) * Real.exp ((d / 4) * (t * (a + b)) -
        (d / 2) * a * t + (3 * d / 2) * b * t) := by
      rw [show (d / 4) * (t * (a + b)) - (d / 2) * a * t + (3 * d / 2) * b * t =
        (d / 4) * (t * (a + b)) + (-(d / 2) * a * t + (3 * d / 2) * b * t) by ring,
        Real.exp_add ((d / 4) * (t * (a + b))) (-(d / 2) * a * t + (3 * d / 2) * b * t)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hL ht.le)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg hd.le hb) ht.le]

end

end Planarwave
