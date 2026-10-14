/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.InverseModulationPDE
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
# Subtracting the stationary profile

Derivative identities for `U(y,z) = φ(z) + v(y,z)` in the inverse-modulated
equation. In particular, the profile contributes no mixed transverse term.
-/

open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_longitudinal_profile_add (φ : ℝ → F) (hφ : Differentiable ℝ φ)
    (v : E × ℝ → F) (hv : Differentiable ℝ v) (y : E) (z : ℝ) :
    deriv (fun r ↦ φ r + v (y, r)) z = deriv φ z + deriv (fun r ↦ v (y, r)) z :=
  deriv_add (hφ z) (((hv _).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))).differentiableAt)

theorem secondDeriv_longitudinal_profile_add (φ : ℝ → F) (hφ : ContDiff ℝ 2 φ)
    (v : E × ℝ → F) (hv : ContDiff ℝ 2 v) (y : E) (z : ℝ) :
    deriv (deriv (fun r ↦ φ r + v (y, r))) z =
      deriv (deriv φ) z + deriv (deriv (fun r ↦ v (y, r))) z := by
  have hs : ContDiff ℝ 2 (fun r ↦ v (y, r)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have hfirst : deriv (fun r ↦ φ r + v (y, r)) =
      fun r ↦ deriv φ r + deriv (fun q ↦ v (y, q)) r :=
    funext (deriv_longitudinal_profile_add φ (hφ.differentiable (by norm_num))
      v (hv.differentiable (by norm_num)) y)
  rw [hfirst]
  exact deriv_add (hφ.differentiable_deriv_two z) (hs.differentiable_deriv_two z)

/-- Identify the mixed Hessian entry with the transverse derivative of `∂z U`. -/
theorem mixed_fderiv_eq (U : E × ℝ → F) (hU : ContDiff ℝ 2 U) (y s : E) (z : ℝ) :
    fderiv ℝ (fderiv ℝ U) (y, z) (s, 0) (0, 1) =
      fderiv ℝ (fun w ↦ deriv (fun r ↦ U (w, r)) z) y s := by
  have hDU : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have h := (ContinuousLinearMap.apply ℝ F ((0 : E), (1 : ℝ))).hasFDerivAt.comp y
    (((hDU.differentiable one_ne_zero _).hasFDerivAt).comp y
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const z y)))
  have hf := h.fderiv
  change fderiv ℝ (fun w ↦ fderiv ℝ U (w, z) (0, 1)) y = _ at hf
  simp only [deriv_longitudinal_eq_fderiv U (hU.differentiable (by norm_num))]
  rw [hf]
  rfl

/-- There is no `∇σ · ∇φ'` term: the profile has no transverse dependence. -/
theorem mixed_fderiv_profile_add (φ : ℝ → F) (hφ : ContDiff ℝ 2 φ)
    (v : E × ℝ → F) (hv : ContDiff ℝ 2 v) (y s : E) (z : ℝ) :
    fderiv ℝ (fderiv ℝ (fun x : E × ℝ ↦ φ x.2 + v x)) (y, z) (s, 0) (0, 1) =
      fderiv ℝ (fderiv ℝ v) (y, z) (s, 0) (0, 1) := by
  have hU : ContDiff ℝ 2 (fun x : E × ℝ ↦ φ x.2 + v x) :=
    (hφ.comp contDiff_snd).add hv
  rw [mixed_fderiv_eq _ hU, mixed_fderiv_eq v hv]
  simp only [deriv_longitudinal_profile_add φ (hφ.differentiable (by norm_num)) v
    (hv.differentiable (by norm_num)), fderiv_const_add]

/-- The profile contributes only its longitudinal second derivative to the Laplacian. -/
theorem splitLaplacian_profile_add [FiniteDimensional ℝ E]
    (φ : ℝ → F) (hφ : ContDiff ℝ 2 φ)
    (v : E × ℝ → F) (hv : ContDiff ℝ 2 v) (y : E) (z : ℝ) :
    splitLaplacian (fun x : E × ℝ ↦ φ x.2 + v x) (y, z) =
      deriv (deriv φ) z + splitLaplacian v (y, z) := by
  have hs : ContDiff ℝ 2 (fun w ↦ v (w, z)) := hv.comp (contDiff_id.prodMk contDiff_const)
  have hl := (contDiffAt_const (c := φ z) (x := y) (n := (2 : WithTop ℕ∞))).laplacian_add hs.contDiffAt
  simp only [Pi.add_def, InnerProductSpace.laplacian_const, Pi.zero_apply, zero_add] at hl
  simp only [splitLaplacian, hl, secondDeriv_longitudinal_profile_add φ hφ v hv]
  abel

end

end Planarwave
