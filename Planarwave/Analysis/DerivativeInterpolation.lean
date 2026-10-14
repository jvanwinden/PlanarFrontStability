/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-!
# Supremum-norm interpolation of spatial derivatives

The elementary adjustable-scale derivative estimate is applied to the
actual iterated Fréchet derivatives. These estimates underlie the C⁹-to-C²
interpolation in Step 4 of the paper's nonlinear iteration.
-/

open Set Metric
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Taylor's first-order estimate at an arbitrary positive scale, with
only a bound on the function and a Lipschitz bound on its derivative. -/
theorem norm_fderiv_le_of_lipschitz_derivative {f : E → F} {A B ε : ℝ}
    (hf : Differentiable ℝ f) (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hbound : ∀ x, ‖f x‖ ≤ A)
    (hderiv : ∀ x y, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ B * ‖y - x‖) (x : E) :
    ‖fderiv ℝ f x‖ ≤ (2 / ε) * A + ε * B := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hx : x ∈ closedBall x ε := mem_closedBall_self hε.le
  have hyv : ‖(x + ε • v) - x‖ = ε := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hv, mul_one]
  have hy : x + ε • v ∈ closedBall x ε := by rw [mem_closedBall, dist_eq_norm, hyv]
  have hrem := (convex_closedBall x ε).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun y (_ : y ∈ closedBall x ε) ↦ (hf y).hasFDerivAt.hasFDerivWithinAt)
    (φ := fderiv ℝ f x) (C := B * ε)
    (fun y hy ↦ (hderiv x y).trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall, dist_eq_norm] using hy) hB)) hx hy
  rw [hyv, add_sub_cancel_left, map_smul] at hrem
  have htriangle := norm_sub_le (f (x + ε • v) - f x)
    (f (x + ε • v) - f x - ε • fderiv ℝ f x v)
  rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at htriangle
  have hb : ε * ‖fderiv ℝ f x v‖ ≤ 2 * A + B * ε * ε :=
    htriangle.trans (add_le_add
      ((norm_sub_le _ _).trans (by linarith [hbound (x + ε • v), hbound x])) hrem)
  apply le_of_mul_le_mul_left (a := ε) _ hε
  calc
    _ ≤ 2 * A + B * ε * ε := hb
    _ = _ := by field_simp

/-- Supremum norm of an actual spatial derivative. Estimates below always
require boundedness of the range; no arbitrary value of `sSup` is used. -/
def derivativeSupNorm (f : E → F) (k : ℕ) : ℝ :=
  sSup (range fun x ↦ ‖iteratedFDeriv ℝ k f x‖)

theorem norm_iteratedFDeriv_le_derivativeSupNorm (f : E → F) (k : ℕ)
    (hb : BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k f x‖)) (x : E) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ derivativeSupNorm f k :=
  le_csSup hb ⟨x, rfl⟩

theorem derivativeSupNorm_nonneg (f : E → F) (k : ℕ)
    (hb : BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k f x‖)) :
    0 ≤ derivativeSupNorm f k :=
  (norm_nonneg _).trans (norm_iteratedFDeriv_le_derivativeSupNorm f k hb 0)

theorem derivativeSupNorm_le (f : E → F) (k : ℕ) {A : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ A) : derivativeSupNorm f k ≤ A := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact hb x

/-- Adjacent orders satisfy the adjustable-scale interpolation estimate.
Currying is isometric, so there is no dimension-dependent norm loss. -/
theorem derivativeSupNorm_interpolate {f : E → F} {N k : ℕ}
    (hf : ContDiff ℝ N f) (hk : k + 2 ≤ N)
    (hb : ∀ j ≤ N, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ j f x‖))
    {ε : ℝ} (hε : 0 < ε) :
    derivativeSupNorm f (k + 1) ≤ (2 / ε) * derivativeSupNorm f k + ε * derivativeSupNorm f (k + 2) := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast (show k < N by omega))
  have hd' : Differentiable ℝ (iteratedFDeriv ℝ (k + 1) f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast (show k + 1 < N by omega))
  apply derivativeSupNorm_le
  intro x
  rw [← norm_fderiv_iteratedFDeriv]
  apply norm_fderiv_le_of_lipschitz_derivative hd
    (derivativeSupNorm_nonneg f k (hb k (by omega)))
    (derivativeSupNorm_nonneg f (k + 2) (hb (k + 2) hk)) hε
    (norm_iteratedFDeriv_le_derivativeSupNorm f k (hb k (by omega)))
  intro y z
  simp only [fderiv_iteratedFDeriv, Function.comp_apply]
  have heq := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F).isometry.dist_eq
    (iteratedFDeriv ℝ (k + 1) f z) (iteratedFDeriv ℝ (k + 1) f y)
  simp only [dist_eq_norm] at heq
  rw [heq]
  exact (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ ↦ hd' w)
    (fun w _ ↦ by
      rw [norm_fderiv_iteratedFDeriv]
      exact norm_iteratedFDeriv_le_derivativeSupNorm f (k + 2) (hb (k + 2) hk) w)
    (mem_univ y) (mem_univ z)

end

end Planarwave
