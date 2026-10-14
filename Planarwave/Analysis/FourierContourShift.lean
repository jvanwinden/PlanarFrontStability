/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.PiContourShift
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Cauchy's theorem for Gaussian Fourier symbols

The oscillatory Fourier factor is holomorphic, and its modulus on a shifted
contour is the real exponential extracted in the paper. A quadratic bound on
that exponential permits the coordinatewise Cauchy argument to be applied to
the full Fourier integrand, not merely to the symbol.
-/

open MeasureTheory

namespace Planarwave

noncomputable section

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The holomorphic Fourier factor in product coordinates, with no conjugation
of the complex frequency. -/
def piFourierPhase (x : Fin n → ℝ) (ζ : Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * ∑ i, ζ i * (x i : ℂ))

/-- Extract the real exponential from the oscillatory factor on a shifted contour. -/
theorem piFourierPhase_shift (x ξ η : Fin n → ℝ) :
    piFourierPhase x (piContourPoint ξ η) =
      Complex.exp (-(∑ i, η i * x i : ℝ)) *
        Complex.exp (Complex.I * (∑ i, ξ i * x i : ℝ)) := by
  unfold piFourierPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [piContourPoint, add_mul, Finset.sum_add_distrib,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, mul_add]
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The modulus of the complex Fourier factor is exactly the extracted real exponential. -/
theorem norm_piFourierPhase (x : Fin n → ℝ) (ζ : Fin n → ℂ) :
    ‖piFourierPhase x ζ‖ = Real.exp (-∑ i, (ζ i).im * x i) := by
  simp [piFourierPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The oscillatory factor remains entire after complexifying every frequency coordinate. -/
theorem differentiable_piFourierPhase (x : Fin n → ℝ) : Differentiable ℂ (piFourierPhase x) := by
  unfold piFourierPhase
  fun_prop

/-- A Gaussian bound on an entire symbol also dominates its full Fourier integrand.
The enlarged imaginary-frequency coefficient is used only to justify the contour shift. -/
theorem piFourierIntegrand_gaussian_bound {g : (Fin n → ℂ) → F} {M b a : ℝ}
    (hM : 0 ≤ M)
    (hbound : ∀ ζ, ‖g ζ‖ ≤ M * Real.exp (-b * ∑ i, (ζ i).re ^ 2 + a * ∑ i, (ζ i).im ^ 2))
    (x : Fin n → ℝ) (ζ : Fin n → ℂ) :
    ‖piFourierPhase x ζ • g ζ‖ ≤
      (M * Real.exp (∑ i, x i ^ 2)) *
        Real.exp (-b * ∑ i, (ζ i).re ^ 2 + (a + 1) * ∑ i, (ζ i).im ^ 2) := by
  have hxy : -(∑ i, (ζ i).im * x i) ≤ (∑ i, (ζ i).im ^ 2) + ∑ i, x i ^ 2 := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg ((ζ i).im + x i), sq_nonneg (ζ i).im, sq_nonneg (x i)]
  rw [norm_smul, norm_piFourierPhase]
  calc
    Real.exp (-∑ i, (ζ i).im * x i) * ‖g ζ‖ ≤
        Real.exp (-∑ i, (ζ i).im * x i) *
          (M * Real.exp (-b * ∑ i, (ζ i).re ^ 2 + a * ∑ i, (ζ i).im ^ 2)) := by
      gcongr
      exact hbound ζ
    _ = M * Real.exp (-(∑ i, (ζ i).im * x i) - b * ∑ i, (ζ i).re ^ 2 +
        a * ∑ i, (ζ i).im ^ 2) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ M * Real.exp ((∑ i, x i ^ 2) +
        (-b * ∑ i, (ζ i).re ^ 2 + (a + 1) * ∑ i, (ζ i).im ^ 2)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
      linarith
    _ = _ := by rw [Real.exp_add]; ring

/-- The multidimensional Fourier contour can be shifted by any real imaginary offset. -/
theorem integral_piFourierContour_eq {g : (Fin n → ℂ) → F} {M b a : ℝ}
    (hM : 0 ≤ M) (hb : 0 < b) (ha : 0 ≤ a) (hg : Differentiable ℂ g)
    (hbound : ∀ ζ, ‖g ζ‖ ≤ M * Real.exp (-b * ∑ i, (ζ i).re ^ 2 + a * ∑ i, (ζ i).im ^ 2))
    (x η₀ η₁ : Fin n → ℝ) :
    (∫ ξ, piFourierPhase x (piContourPoint ξ η₀) • g (piContourPoint ξ η₀)) =
      ∫ ξ, piFourierPhase x (piContourPoint ξ η₁) • g (piContourPoint ξ η₁) := by
  apply integral_piContour_eq_of_gaussian_bound
    (M := M * Real.exp (∑ i, x i ^ 2)) (b := b) (a := a + 1)
    (by positivity) hb (by positivity)
    ((differentiable_piFourierPhase x).smul hg)
  exact piFourierIntegrand_gaussian_bound hM hbound x

end

end Planarwave
