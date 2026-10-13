/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DerivativeInterpolation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# C⁹-to-C² interpolation in the nonlinear iteration

Apply the adjacent-order interpolation estimate at eight different scales
and eliminate the intermediate derivatives. The constants are deliberately
non-optimal; only their independence of the solution matters in Step 4.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

/-- Finite elimination of the eight adjacent-order estimates. -/
theorem nine_derivative_interpolation_algebra (b : ℕ → ℝ)
    (hzero : 0 ≤ b 0) (hnine : 0 ≤ b 9)
    (hstep : ∀ k < 8, b (k + 1) ≤ (2 / (8 : ℝ) ^ k) * b k + (8 : ℝ) ^ k * b (k + 2)) :
    b 1 ≤ (8 : ℝ) ^ 36 * (b 0 + b 9) ∧ b 2 ≤ (8 : ℝ) ^ 36 * (b 0 + b 9) := by
  have h0 := hstep 0 (by omega)
  have h1 := hstep 1 (by omega)
  have h2 := hstep 2 (by omega)
  have h3 := hstep 3 (by omega)
  have h4 := hstep 4 (by omega)
  have h5 := hstep 5 (by omega)
  have h6 := hstep 6 (by omega)
  have h7 := hstep 7 (by omega)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  constructor <;> linarith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Scaled first- and second-derivative bounds in terms of orders zero
and nine, with all intermediate derivative norms eliminated. -/
theorem derivativeSupNorm_nine_scaled {f : E → F} (hf : ContDiff ℝ 9 f)
    (hb : ∀ k ≤ 9, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k f x‖))
    {ε : ℝ} (hε : 0 < ε) :
    ε * derivativeSupNorm f 1 ≤ (8 : ℝ) ^ 36 * (derivativeSupNorm f 0 + ε ^ 9 * derivativeSupNorm f 9) ∧
    ε ^ 2 * derivativeSupNorm f 2 ≤ (8 : ℝ) ^ 36 * (derivativeSupNorm f 0 + ε ^ 9 * derivativeSupNorm f 9) := by
  let b := fun k ↦ ε ^ k * derivativeSupNorm f k
  have hstep (k : ℕ) (hk : k < 8) :
      b (k + 1) ≤ (2 / (8 : ℝ) ^ k) * b k + (8 : ℝ) ^ k * b (k + 2) := by
    have hi := derivativeSupNorm_interpolate hf (by omega : k + 2 ≤ 9) hb
      (by positivity : 0 < ε * (8 : ℝ) ^ k)
    have h := mul_le_mul_of_nonneg_left hi (pow_nonneg hε.le (k + 1))
    calc
      _ ≤ ε ^ (k + 1) * ((2 / (ε * (8 : ℝ) ^ k)) * derivativeSupNorm f k +
          (ε * (8 : ℝ) ^ k) * derivativeSupNorm f (k + 2)) := h
      _ = _ := by
        dsimp only [b]
        simp only [pow_add, pow_one, pow_two]
        field_simp
  have h := nine_derivative_interpolation_algebra b
    (by dsimp only [b]; exact mul_nonneg (by positivity) (derivativeSupNorm_nonneg f 0 (hb 0 (by omega))))
    (by dsimp only [b]; exact mul_nonneg (by positivity) (derivativeSupNorm_nonneg f 9 (hb 9 le_rfl))) hstep
  simpa only [b, pow_zero, one_mul, pow_one] using h

/-- Optimizing the scale gives the `7/9` interpolation exponent. The
slack between `7/9` and `3/4` is used to absorb the logarithm in the paper.
Only boundedness, not a quantitative bound, is needed at orders one to eight. -/
theorem derivativeSupNorm_c2_le_of_nine {f : E → F} (hf : ContDiff ℝ 9 f)
    (hb : ∀ k ≤ 9, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k f x‖))
    {A B : ℝ} (hA : 0 ≤ A) (hA1 : A ≤ 1) (hB : 0 ≤ B)
    (hzero : ∀ x, ‖f x‖ ≤ A) (hnine : ∀ x, ‖iteratedFDeriv ℝ 9 f x‖ ≤ B) :
    derivativeSupNorm f 0 + derivativeSupNorm f 1 + derivativeSupNorm f 2 ≤
      (1 + 2 * (8 : ℝ) ^ 36 * (1 + B)) * A ^ ((7 : ℝ) / 9) := by
  by_cases hAz : A = 0
  · have hfzero : f = 0 := by
      funext x
      exact norm_eq_zero.mp (le_antisymm (by simpa only [hAz] using hzero x) (norm_nonneg _))
    simp [hfzero, derivativeSupNorm, hAz, Real.zero_rpow (by norm_num : (7 : ℝ) / 9 ≠ 0)]
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  let ε := A ^ ((1 : ℝ) / 9)
  have hε : 0 < ε := Real.rpow_pos_of_pos hApos _
  have hε9 : ε ^ 9 = A := by
    dsimp only [ε]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  have hε1 : ε * A ^ ((8 : ℝ) / 9) = A := by
    dsimp only [ε]
    rw [← Real.rpow_add hApos]
    norm_num
  have hε2 : ε ^ 2 * A ^ ((7 : ℝ) / 9) = A := by
    dsimp only [ε]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA, ← Real.rpow_add hApos]
    norm_num
  have h0 : derivativeSupNorm f 0 ≤ A :=
    derivativeSupNorm_le f 0 (by simpa only [norm_iteratedFDeriv_zero] using hzero)
  have h9 : derivativeSupNorm f 9 ≤ B := derivativeSupNorm_le f 9 hnine
  obtain ⟨h1, h2⟩ := derivativeSupNorm_nine_scaled hf hb hε
  rw [hε9] at h1 h2
  have hbound : (8 : ℝ) ^ 36 * (derivativeSupNorm f 0 + A * derivativeSupNorm f 9) ≤
      (8 : ℝ) ^ 36 * (1 + B) * A := by
    calc
      _ ≤ (8 : ℝ) ^ 36 * (A + A * B) := by gcongr
      _ = _ := by ring
  have hfirst : derivativeSupNorm f 1 ≤ (8 : ℝ) ^ 36 * (1 + B) * A ^ ((8 : ℝ) / 9) := by
    apply le_of_mul_le_mul_left (a := ε) _ hε
    calc
      _ ≤ (8 : ℝ) ^ 36 * (1 + B) * A := h1.trans hbound
      _ = _ := by rw [mul_left_comm ε, hε1]
  have hsecond : derivativeSupNorm f 2 ≤ (8 : ℝ) ^ 36 * (1 + B) * A ^ ((7 : ℝ) / 9) := by
    apply le_of_mul_le_mul_left (a := ε ^ 2) _ (by positivity)
    calc
      _ ≤ (8 : ℝ) ^ 36 * (1 + B) * A := h2.trans hbound
      _ = _ := by rw [mul_left_comm (ε ^ 2), hε2]
  have h08 : A ≤ A ^ ((7 : ℝ) / 9) := Real.self_le_rpow_of_le_one hA hA1 (by norm_num)
  have h18 : A ^ ((8 : ℝ) / 9) ≤ A ^ ((7 : ℝ) / 9) :=
    Real.rpow_le_rpow_of_exponent_ge hApos hA1 (by norm_num)
  have hfirst' := hfirst.trans (mul_le_mul_of_nonneg_left h18
    (by positivity : 0 ≤ (8 : ℝ) ^ 36 * (1 + B)))
  nlinarith [h0.trans h08]

end

end Planarwave
