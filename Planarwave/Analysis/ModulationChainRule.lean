/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

/-!
# Chain rules for the inverse-modulation shear

Section 4 of the paper differentiates `u(t,y,z) = U(t,y,z-c*t-σ(t,y))`.
These identities are derived from actual Fréchet derivatives. In particular,
the mixed second derivative and the phase Hessian term are not independent
fields or extra transformation assumptions.
-/

open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

variable {X Y F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second chain rule along a curve, with an explicit curve two-jet. -/
theorem secondDeriv_comp_curve (U : X → F) (hU : ContDiff ℝ 2 U)
    (γ γ₁ : ℝ → X) (hγ : ∀ t, HasDerivAt γ (γ₁ t) t)
    (t : ℝ) (γ₂ : X) (hγ₁ : HasDerivAt γ₁ γ₂ t) :
    deriv (deriv (fun r ↦ U (γ r))) t =
      fderiv ℝ (fderiv ℝ U) (γ t) (γ₁ t) (γ₁ t) + fderiv ℝ U (γ t) γ₂ := by
  have hDU : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hfirst : deriv (fun r ↦ U (γ r)) = fun r ↦ fderiv ℝ U (γ r) (γ₁ r) :=
    funext fun r ↦ ((hU.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r (hγ r)).deriv
  rw [hfirst]
  exact (((hDU.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t (hγ t)).clm_apply hγ₁).deriv

/-- On an affine line, the second derivative is the Hessian evaluated twice
on its direction. This statement also applies to Banach-valued functions. -/
theorem secondDeriv_affine_line (U : X → F) (hU : ContDiff ℝ 2 U) (x v : X) :
    deriv (deriv (fun r : ℝ ↦ U (x + r • v))) 0 = fderiv ℝ (fderiv ℝ U) x v v := by
  simpa using secondDeriv_comp_curve U hU (fun r ↦ x + r • v) (fun _ ↦ v)
    (fun r ↦ by simpa using ((hasDerivAt_id r).smul_const v).const_add x)
    0 0 (hasDerivAt_const 0 v)

/-- Expand the quadratic form in a sheared transverse direction. -/
theorem bilinear_shear_diagonal (H : (Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)
    (hsym : ∀ a b, H a b = H b a) (v : Y) (p : ℝ) :
    H (v, -p) (v, -p) = H (v, 0) (v, 0) - (2 * p) • H (v, 0) (0, 1) +
      p ^ 2 • H (0, 1) (0, 1) := by
  have hdir : (v, -p) = (v, (0 : ℝ)) - p • ((0 : Y), (1 : ℝ)) := by ext <;> simp
  rw [hdir]
  simp only [map_sub, map_smul, sub_apply, smul_apply,
    smul_sub, hsym (0, 1) (v, 0), pow_two, mul_smul, two_smul]
  abel

/-- The second transverse directional chain rule for the backward shear.
The `-2` mixed term is exactly the one in the paper's coordinate calculation. -/
theorem secondDeriv_transverse_shear (U : Y × ℝ → F) (hU : ContDiff ℝ 2 U)
    (σ : Y → ℝ) (hσ : ContDiff ℝ 2 σ) (a z : ℝ) (y v : Y) :
    deriv (deriv (fun r : ℝ ↦ U (y + r • v, z - a - σ (y + r • v)))) 0 =
      fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (v, 0) (v, 0) -
      (2 * fderiv ℝ σ y v) • fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (v, 0) (0, 1) +
      (fderiv ℝ σ y v) ^ 2 • fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (0, 1) (0, 1) -
      fderiv ℝ (fderiv ℝ σ) y v v • fderiv ℝ U (y, z - a - σ y) (0, 1) := by
  let γ := fun r : ℝ ↦ (y + r • v, z - a - σ (y + r • v))
  let γ₁ := fun r : ℝ ↦ (v, -fderiv ℝ σ (y + r • v) v)
  have hline (r : ℝ) : HasDerivAt (fun s : ℝ ↦ y + s • v) v r := by
    simpa using ((hasDerivAt_id r).smul_const v).const_add y
  have hγ (r : ℝ) : HasDerivAt γ (γ₁ r) r :=
    (hline r).prodMk (((hσ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r (hline r)).const_sub (z - a))
  have hDσ : ContDiff ℝ 1 (fderiv ℝ σ) := hσ.fderiv_right (by norm_num)
  have hγ₁ : HasDerivAt γ₁ (0, -fderiv ℝ (fderiv ℝ σ) y v v) 0 := by
    simpa only [γ₁, zero_smul, add_zero, map_zero, add_zero] using!
      (hasDerivAt_const 0 v).prodMk
        ((((hDσ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt 0 (hline 0)).clm_apply
          (hasDerivAt_const 0 v)).neg)
  have h := secondDeriv_comp_curve U hU γ γ₁ hγ 0 _ hγ₁
  have hDU : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hsym := second_derivative_symmetric
    (fun x ↦ (hU.differentiable (by norm_num) x).hasFDerivAt)
    ((hDU.differentiable one_ne_zero (y, z - a - σ y)).hasFDerivAt)
  simp only [γ, γ₁, zero_smul, add_zero] at h
  rw [bilinear_shear_diagonal _ hsym] at h
  rw [h]
  have hdir (b : ℝ) : ((0 : Y), -b) = (-b) • ((0 : Y), (1 : ℝ)) := by ext <;> simp
  rw [hdir, map_smul]
  simp only [neg_smul, sub_eq_add_neg]

/-- Laplacians can be computed by taking second derivatives along basis lines. -/
theorem laplacian_eq_sum_secondDeriv {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : E → F) (hf : ContDiff ℝ 2 f) (x : E) :
    Δ f x = ∑ i, deriv (deriv (fun r : ℝ ↦ f (x + r • b i))) 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  apply Finset.sum_congr rfl
  intro i _
  simp only [secondDeriv_affine_line f hf, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The transverse Laplacian of a backward-modulated field. This is the sum
of the coordinate identities preceding `eq:utildepde` in the paper. -/
theorem laplacian_transverse_shear {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : E × ℝ → F) (hU : ContDiff ℝ 2 U)
    (σ : E → ℝ) (hσ : ContDiff ℝ 2 σ) (a z : ℝ) (y : E) :
    Δ (fun w ↦ U (w, z - a - σ w)) y =
      Δ (fun w ↦ U (w, z - a - σ y)) y -
      (2 : ℝ) • fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (∇ σ y, 0) (0, 1) +
      ‖∇ σ y‖ ^ 2 • fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (0, 1) (0, 1) -
      Δ σ y • fderiv ℝ U (y, z - a - σ y) (0, 1) := by
  let b := stdOrthonormalBasis ℝ E
  have hcomp : ContDiff ℝ 2 (fun w ↦ U (w, z - a - σ w)) :=
    hU.comp (contDiff_id.prodMk (contDiff_const.sub hσ))
  have hslice : ContDiff ℝ 2 (fun w ↦ U (w, z - a - σ y)) :=
    hU.comp (contDiff_id.prodMk contDiff_const)
  have hsliceLine (v : E) :
      deriv (deriv (fun r : ℝ ↦ U (y + r • v, z - a - σ y))) 0 =
        fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (v, 0) (v, 0) := by
    simpa using secondDeriv_affine_line U hU (y, z - a - σ y) (v, 0)
  have hgrad : ∑ i, fderiv ℝ σ y (b i) • b i = ∇ σ y := by
    simpa only [real_inner_comm, inner_gradient_left] using b.sum_repr' (∇ σ y)
  have hnorm : ∑ i, (fderiv ℝ σ y (b i)) ^ 2 = ‖∇ σ y‖ ^ 2 := by
    simpa only [inner_gradient_left] using b.sum_sq_inner_left (∇ σ y)
  have htrace : ∑ i, fderiv ℝ (fderiv ℝ σ) y (b i) (b i) = Δ σ y := by
    rw [laplacian_eq_sum_secondDeriv b σ hσ]
    simp only [secondDeriv_affine_line σ hσ]
  let H := fderiv ℝ (fderiv ℝ U) (y, z - a - σ y)
  let B : E →L[ℝ] F :=
    ((ContinuousLinearMap.apply ℝ F (0, 1)).comp H).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hB (v : E) : B v = H (v, 0) (0, 1) := rfl
  have hmixed : ∑ i, (2 * fderiv ℝ σ y (b i)) • H (b i, 0) (0, 1) =
      (2 : ℝ) • H (∇ σ y, 0) (0, 1) := by
    simp only [mul_smul, ← hB, ← Finset.smul_sum, ← map_smul, ← map_sum, hgrad]
  rw [laplacian_eq_sum_secondDeriv b _ hcomp, laplacian_eq_sum_secondDeriv b _ hslice]
  simp only [secondDeriv_transverse_shear U hU σ hσ, hsliceLine,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul]
  rw [hmixed, hnorm, htrace]

/-- Differentiation in the longitudinal direction commutes with the shear. -/
theorem secondDeriv_longitudinal_shear (U : Y × ℝ → F) (hU : ContDiff ℝ 2 U)
    (y : Y) (a z : ℝ) :
    deriv (deriv (fun r ↦ U (y, r - a))) z =
      fderiv ℝ (fderiv ℝ U) (y, z - a) (0, 1) (0, 1) := by
  simpa using secondDeriv_comp_curve U hU (fun r ↦ (y, r - a)) (fun _ ↦ (0, 1))
    (fun r ↦ (hasDerivAt_const r y).prodMk ((hasDerivAt_id r).sub_const a))
    z 0 (hasDerivAt_const z (0, 1))

/-- The time chain rule for the same backward shear, at a fixed transverse point. -/
theorem deriv_time_shear (U : ℝ × (Y × ℝ) → F)
    (σ : ℝ → ℝ) (t σt c z : ℝ) (hσ : HasDerivAt σ σt t) (y : Y)
    (hU : DifferentiableAt ℝ U (t, y, z - c * t - σ t)) :
    deriv (fun r ↦ U (r, y, z - c * r - σ r)) t =
      fderiv ℝ U (t, y, z - c * t - σ t) (1, 0, 0) -
      (c + σt) • fderiv ℝ U (t, y, z - c * t - σ t) (0, 0, 1) := by
  have hcurve : HasDerivAt (fun r ↦ (r, y, z - c * r - σ r)) (1, 0, -(c + σt)) t := by
    convert (hasDerivAt_id t).prodMk ((hasDerivAt_const t y).prodMk
      ((((hasDerivAt_id t).const_mul c).const_sub z).sub hσ)) using 1 <;> simp
    ring
  have ht := (hU.hasFDerivAt.comp_hasDerivAt t hcurve).deriv
  simp only [Function.comp_def] at ht
  rw [ht]
  have hdir : ((1 : ℝ), (0 : Y), -(c + σt)) =
      (1, 0, 0) - (c + σt) • (0, 0, 1) := by ext <;> simp
  rw [hdir, map_sub, map_smul]

end

end Planarwave
