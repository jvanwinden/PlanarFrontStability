/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ModulationChainRule

@[expose] public section

/-!
# The equation in inverse-modulated coordinates

The chain-rule calculation in Section 4, up to `eq:utildepde2`. These are
identities for classical fields, conditional on the reaction--diffusion and
phase equations, not existence results for either equation. The split
Laplacian is used because the ordinary product space has the maximum norm,
not the Euclidean product inner product.
-/

open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Euclidean Laplacian written as transverse plus longitudinal derivatives. -/
def splitLaplacian (U : E × ℝ → F) (x : E × ℝ) : F :=
  Δ (fun y ↦ U (y, x.2)) x.1 + deriv (deriv (fun z ↦ U (x.1, z))) x.2

omit [FiniteDimensional ℝ E] in
/-- The first longitudinal derivative is an evaluation of the spatial derivative. -/
theorem deriv_longitudinal_eq_fderiv (U : E × ℝ → F) (hU : Differentiable ℝ U)
    (y : E) (z : ℝ) :
    deriv (fun r ↦ U (y, r)) z = fderiv ℝ U (y, z) (0, 1) :=
  ((hU _).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))).deriv

/-- The full split Laplacian under the paper's backward shear. -/
theorem splitLaplacian_shear (U : E × ℝ → F) (hU : ContDiff ℝ 2 U)
    (σ : E → ℝ) (hσ : ContDiff ℝ 2 σ) (a z : ℝ) (y : E) :
    splitLaplacian (fun x ↦ U (x.1, x.2 - a - σ x.1)) (y, z) =
      splitLaplacian U (y, z - a - σ y) -
      (2 : ℝ) • fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (∇ σ y, 0) (0, 1) +
      ‖∇ σ y‖ ^ 2 • deriv (deriv (fun r ↦ U (y, r))) (z - a - σ y) -
      Δ σ y • deriv (fun r ↦ U (y, r)) (z - a - σ y) := by
  have hzz : deriv (deriv (fun r ↦ U (y, r - a - σ y))) z =
      fderiv ℝ (fderiv ℝ U) (y, z - a - σ y) (0, 1) (0, 1) := by
    simpa only [sub_sub] using secondDeriv_longitudinal_shear U hU y (a + σ y) z
  have hzz₀ (w : ℝ) : deriv (deriv (fun r ↦ U (y, r))) w =
      fderiv ℝ (fderiv ℝ U) (y, w) (0, 1) (0, 1) := by
    simpa only [sub_zero] using secondDeriv_longitudinal_shear U hU y 0 w
  simp only [splitLaplacian, laplacian_transverse_shear U hU σ hσ, hzz, hzz₀,
    deriv_longitudinal_eq_fderiv U (hU.differentiable (by norm_num))]
  abel

omit [FiniteDimensional ℝ E] in
/-- The time chain rule expressed entirely in classical partial derivatives. -/
theorem deriv_time_shear_classical (U : ℝ × (E × ℝ) → F)
    (σ : ℝ → ℝ) (t σt c z : ℝ) (hσ : HasDerivAt σ σt t) (y : E)
    (hU : DifferentiableAt ℝ U (t, y, z - c * t - σ t)) :
    deriv (fun r ↦ U (r, y, z - c * r - σ r)) t =
      deriv (fun r ↦ U (r, y, z - c * t - σ t)) t -
      (c + σt) • deriv (fun r ↦ U (t, y, r)) (z - c * t - σ t) := by
  let w := z - c * t - σ t
  have ht : deriv (fun r ↦ U (r, y, w)) t =
      fderiv ℝ U (t, y, w) (1, 0, 0) :=
    (hU.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (y, w)))).deriv
  have hz : deriv (fun r ↦ U (t, y, r)) w =
      fderiv ℝ U (t, y, w) (0, 0, 1) :=
    (hU.hasFDerivAt.comp_hasDerivAt w
      ((hasDerivAt_const w t).prodMk
        ((hasDerivAt_const w y).prodMk (hasDerivAt_id w)))).deriv
  rw [ht, hz]
  exact deriv_time_shear U σ t σt c z hσ y hU

/-- Equation `eq:utildepde`, obtained by substituting the actual chain rules
in the physical reaction--diffusion equation and shifting back. -/
theorem inverseModulated_rde (U : ℝ × (E × ℝ) → F)
    (σ : ℝ → E → ℝ) (f : F → F) (D : F →L[ℝ] F) (c t : ℝ)
    (hUs : ContDiff ℝ 2 (fun x ↦ U (t, x))) (hσs : ContDiff ℝ 2 (σ t))
    (y : E) (z σt : ℝ) (hσt : HasDerivAt (fun r ↦ σ r y) σt t)
    (hU : DifferentiableAt ℝ U (t, y, z))
    (hrde : ∀ w, deriv (fun r ↦ U (r, y, w - c * r - σ r y)) t =
      D (splitLaplacian (fun x ↦ U (t, x.1, x.2 - c * t - σ t x.1)) (y, w)) +
      f (U (t, y, w - c * t - σ t y))) :
    deriv (fun r ↦ U (r, y, z)) t - (c + σt) • deriv (fun r ↦ U (t, y, r)) z =
      D (splitLaplacian (fun x ↦ U (t, x)) (y, z)) + f (U (t, y, z)) -
      Δ (σ t) y • D (deriv (fun r ↦ U (t, y, r)) z) -
      (2 : ℝ) • D (fderiv ℝ (fderiv ℝ (fun x ↦ U (t, x))) (y, z) (∇ (σ t) y, 0) (0, 1)) +
      ‖∇ (σ t) y‖ ^ 2 • D (deriv (deriv (fun r ↦ U (t, y, r))) z) := by
  have heval : z + c * t + σ t y - c * t - σ t y = z := by ring
  have h := hrde (z + c * t + σ t y)
  rw [deriv_time_shear_classical U _ t σt c _ hσt y (by simpa only [heval] using hU),
    splitLaplacian_shear _ hUs _ hσs, heval] at h
  rw [h]
  simp only [map_sub, map_add, map_smul]
  abel

/-- Substituting the forced phase equation gives `eq:utildepde2` with the
paper's precise drift, mixed term, and negative forcing sign. -/
theorem inverseModulated_rde_forced (U : ℝ × (E × ℝ) → F)
    (σ : ℝ → E → ℝ) (f : F → F) (D : F →L[ℝ] F) (c a t : ℝ)
    (hUs : ContDiff ℝ 2 (fun x ↦ U (t, x))) (hσs : ContDiff ℝ 2 (σ t))
    (y : E) (z σt g : ℝ) (hσt : HasDerivAt (fun r ↦ σ r y) σt t)
    (hU : DifferentiableAt ℝ U (t, y, z))
    (hphase : σt = a * Δ (σ t) y + (c / 2) * ‖∇ (σ t) y‖ ^ 2 - g)
    (hrde : ∀ w, deriv (fun r ↦ U (r, y, w - c * r - σ r y)) t =
      D (splitLaplacian (fun x ↦ U (t, x.1, x.2 - c * t - σ t x.1)) (y, w)) +
      f (U (t, y, w - c * t - σ t y))) :
    deriv (fun r ↦ U (r, y, z)) t =
      D (splitLaplacian (fun x ↦ U (t, x)) (y, z)) + c • deriv (fun r ↦ U (t, y, r)) z +
      f (U (t, y, z)) +
      Δ (σ t) y • (a • deriv (fun r ↦ U (t, y, r)) z - D (deriv (fun r ↦ U (t, y, r)) z)) +
      ‖∇ (σ t) y‖ ^ 2 • (D (deriv (deriv (fun r ↦ U (t, y, r))) z) +
        (c / 2) • deriv (fun r ↦ U (t, y, r)) z) -
      (2 : ℝ) • D (fderiv ℝ (fderiv ℝ (fun x ↦ U (t, x))) (y, z) (∇ (σ t) y, 0) (0, 1)) -
      g • deriv (fun r ↦ U (t, y, r)) z := by
  have h := inverseModulated_rde U σ f D c t hUs hσs y z σt hσt hU hrde
  rw [sub_eq_iff_eq_add] at h
  rw [h, hphase]
  simp only [add_smul, sub_smul, smul_add, smul_sub, mul_smul]
  rw [smul_comm a (Δ (σ t) y), smul_comm (c / 2) (‖∇ (σ t) y‖ ^ 2)]
  abel

end

end Planarwave
