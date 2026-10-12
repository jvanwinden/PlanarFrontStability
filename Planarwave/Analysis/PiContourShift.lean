/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HorizontalContourShift
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Coordinatewise shifts of a multidimensional Fourier contour

Fubini expresses the absolutely convergent integral as a superposition of
one-dimensional contours. Shift one coordinate at a time, then use finite
induction to shift the whole contour. This is the multidimensional step in
Section 3's Cauchy argument.
-/

open MeasureTheory Function

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Fubini with any chosen coordinate as the inner real integral. -/
theorem integral_pi_eq_integral_insertNth {n : ℕ} {g : (Fin (n + 1) → ℝ) → F}
    (hg : Integrable g) (i : Fin (n + 1)) :
    (∫ ξ, g ξ) = ∫ y : Fin n → ℝ, ∫ r : ℝ, g (i.insertNth r y) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove _ i).symm
  have hi := (he.integrable_comp_emb e.measurableEmbedding).mpr hg
  rw [← he.integral_comp' g]
  exact integral_prod_symm (g ∘ e) hi

/-- The point with real part `ξ` and fixed imaginary part `η`, in product coordinates. -/
def piContourPoint {n : ℕ} (ξ η : Fin n → ℝ) : Fin n → ℂ :=
  fun i ↦ (ξ i : ℂ) + (η i : ℂ) * Complex.I

omit [CompleteSpace F] in
/-- Shifting one imaginary coordinate does not change the multidimensional integral
if the one-dimensional slice integrals agree. -/
theorem integral_piContour_update {n : ℕ} {g : (Fin n → ℂ) → F}
    (hint : ∀ η, Integrable (fun ξ ↦ g (piContourPoint ξ η)))
    (hline : ∀ (i : Fin n) (z : Fin n → ℂ) (β γ : ℝ),
      (∫ r : ℝ, g (update z i (r + β * Complex.I))) =
        ∫ r : ℝ, g (update z i (r + γ * Complex.I)))
    (η : Fin n → ℝ) (i : Fin n) (a : ℝ) :
    (∫ ξ, g (piContourPoint ξ η)) = ∫ ξ, g (piContourPoint ξ (update η i a)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [integral_pi_eq_integral_insertNth (hint η) i,
      integral_pi_eq_integral_insertNth (hint (update η i a)) i]
    apply integral_congr_ae
    filter_upwards [] with y
    convert hline i (piContourPoint (i.insertNth 0 y) η) (η i) a using 1 <;>
      apply integral_congr_ae <;> filter_upwards [] with r <;> congr 1 <;>
      ext j <;> by_cases hj : j = i <;> simp [piContourPoint, hj]
    all_goals
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      simp

omit [CompleteSpace F] in
/-- Fubini and successive one-coordinate shifts identify any two parallel real contours. -/
theorem integral_piContour_eq {n : ℕ} {g : (Fin n → ℂ) → F}
    (hint : ∀ η, Integrable (fun ξ ↦ g (piContourPoint ξ η)))
    (hline : ∀ (i : Fin n) (z : Fin n → ℂ) (β γ : ℝ),
      (∫ r : ℝ, g (update z i (r + β * Complex.I))) =
        ∫ r : ℝ, g (update z i (r + γ * Complex.I)))
    (η₀ η₁ : Fin n → ℝ) :
    (∫ ξ, g (piContourPoint ξ η₀)) = ∫ ξ, g (piContourPoint ξ η₁) := by
  classical
  have hs (s : Finset (Fin n)) :
      (∫ ξ, g (piContourPoint ξ (fun j ↦ if j ∈ s then η₁ j else η₀ j))) =
        ∫ ξ, g (piContourPoint ξ η₀) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      have heq : (fun j ↦ if j ∈ insert i s then η₁ j else η₀ j) =
          update (fun j ↦ if j ∈ s then η₁ j else η₀ j) i (η₁ i) := by
        ext j
        by_cases hj : j = i <;> simp [hj]
      rw [heq, ← integral_piContour_update hint hline]
      exact ih
  simpa using (hs Finset.univ).symm

/-- The product-coordinate Gaussian is integrable in every dimension. -/
theorem integrable_piGaussian {n : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : Fin n → ℝ ↦ Real.exp (-b * ∑ i, ξ i ^ 2)) := by
  simpa only [← Real.exp_sum, ← Finset.mul_sum] using!
    (Integrable.fintype_prod (f := fun _ : Fin n ↦ fun r : ℝ ↦ Real.exp (-b * r ^ 2))
      (fun _ ↦ integrable_exp_neg_mul_sq hb))

omit [CompleteSpace F] [NormedSpace ℂ F] in
/-- A Gaussian-dominated entire function is integrable on each parallel real contour. -/
theorem integrable_piContour_of_gaussian_bound {n : ℕ} {g : (Fin n → ℂ) → F}
    {M b a : ℝ} (hb : 0 < b) (hg : Continuous g)
    (hbound : ∀ z, ‖g z‖ ≤ M * Real.exp (-b * ∑ i, (z i).re ^ 2 + a * ∑ i, (z i).im ^ 2))
    (η : Fin n → ℝ) : Integrable (fun ξ ↦ g (piContourPoint ξ η)) := by
  have hc : Continuous (fun ξ ↦ g (piContourPoint ξ η)) := hg.comp (by unfold piContourPoint; fun_prop)
  apply ((integrable_piGaussian (n := n) hb).const_mul
    (M * Real.exp (a * ∑ i, η i ^ 2))).mono' hc.aestronglyMeasurable
  filter_upwards [] with ξ
  apply (hbound (piContourPoint ξ η)).trans_eq
  simp only [piContourPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_self,
    add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

omit [CompleteSpace F] in
/-- Gaussian domination controls the vertical sides of every one-coordinate strip. -/
theorem integral_piSlice_eq_of_gaussian_bound {n : ℕ} {g : (Fin n → ℂ) → F}
    {M b a : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (ha : 0 ≤ a) (hg : Differentiable ℂ g)
    (hbound : ∀ z, ‖g z‖ ≤ M * Real.exp (-b * ∑ i, (z i).re ^ 2 + a * ∑ i, (z i).im ^ 2))
    (i : Fin n) (z : Fin n → ℂ) (β γ : ℝ) :
    (∫ r : ℝ, g (update z i (r + β * Complex.I))) =
      ∫ r : ℝ, g (update z i (r + γ * Complex.I)) := by
  have hd : Differentiable ℂ (fun w : ℂ ↦ g (update z i w)) := by
    apply hg.comp
    apply differentiable_pi.mpr
    intro j
    by_cases hj : j = i <;> simp [hj]
  have hstrip (β γ : ℝ) (hβγ : β ≤ γ) :
      (∫ r : ℝ, g (update z i (r + β * Complex.I))) =
        ∫ r : ℝ, g (update z i (r + γ * Complex.I)) := by
    apply integral_horizontal_eq_of_gaussian_bound hβγ hb (fun w _ _ ↦ hd w)
      (C := M * Real.exp (a * ((|β| + |γ|) ^ 2 + ∑ j, (z j).im ^ 2)))
    intro w hβ hγ
    have hre : w.re ^ 2 ≤ ∑ j, ((update z i w) j).re ^ 2 := by
      simpa using (Finset.single_le_sum (s := Finset.univ)
        (f := fun j ↦ ((update z i w) j).re ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i))
    have him : (∑ j, ((update z i w) j).im ^ 2) ≤ w.im ^ 2 + ∑ j, (z j).im ^ 2 := by
      have hp (j : Fin n) : ((update z i w) j).im ^ 2 ≤
          (if j = i then w.im ^ 2 else 0) + (z j).im ^ 2 := by
        by_cases hj : j = i <;> simp [hj, sq_nonneg]
      simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hp j)
    have hw : |w.im| ≤ |β| + |γ| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le β, le_abs_self γ, abs_nonneg β, abs_nonneg γ]
    have hw2 : w.im ^ 2 ≤ (|β| + |γ|) ^ 2 := by
      nlinarith [sq_abs w.im, abs_nonneg w.im, abs_nonneg β, abs_nonneg γ]
    apply (hbound (update z i w)).trans
    calc
      M * Real.exp (-b * ∑ j, ((update z i w) j).re ^ 2 +
          a * ∑ j, ((update z i w) j).im ^ 2) ≤
          M * Real.exp (a * ((|β| + |γ|) ^ 2 + ∑ j, (z j).im ^ 2) - b * w.re ^ 2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
        nlinarith [mul_le_mul_of_nonneg_left hre hb.le, mul_le_mul_of_nonneg_left him ha,
          mul_le_mul_of_nonneg_left hw2 ha]
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rcases le_total β γ with h | h
  · exact hstrip β γ h
  · exact (hstrip γ β h).symm

omit [CompleteSpace F] in
/-- Multidimensional Cauchy shift for an entire Gaussian-dominated Banach-valued function.
Every use of Fubini is justified by absolute convergence on the corresponding contour. -/
theorem integral_piContour_eq_of_gaussian_bound {n : ℕ} {g : (Fin n → ℂ) → F}
    {M b a : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (ha : 0 ≤ a) (hg : Differentiable ℂ g)
    (hbound : ∀ z, ‖g z‖ ≤ M * Real.exp (-b * ∑ i, (z i).re ^ 2 + a * ∑ i, (z i).im ^ 2))
    (η₀ η₁ : Fin n → ℝ) :
    (∫ ξ, g (piContourPoint ξ η₀)) = ∫ ξ, g (piContourPoint ξ η₁) :=
  integral_piContour_eq (integrable_piContour_of_gaussian_bound hb hg.continuous hbound)
    (integral_piSlice_eq_of_gaussian_bound hM hb ha hg hbound) η₀ η₁

end

end Planarwave
