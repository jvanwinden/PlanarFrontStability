/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearity
import all Planarwave.Analysis.CoordinateLaplacian
import Planarwave.Analysis.ModulationProfileDerivatives

/-!
# The inverse-modulated perturbation equation for the actual front

Derive `eq:pdev` of the paper for classical reaction--diffusion and forced
phase solutions in split coordinates. The remainder is exactly the BUC
nonlinearity used by the proved Lemmas 4.1 and 4.2. This does not construct the
solutions or the forcing; those are separate existence obligations.
-/

open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)

/-- The exact inverse-modulated perturbation equation, with genuine spatial
derivative fields and the original front's transverse diffusion coefficient.
`hmod` is the paper's inverse-modulation Ansatz, not a PDE transformation
assumption; the latter is proved by the chain rules. -/
theorem frontInverseModulatedPerturbation_pde
    (u : ℝ → ℝ^m × ℝ → ℝ^n) (v : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
    (σ : ℝ → ℝ^m → ℝ) (t : ℝ)
    (hvs : ContDiff ℝ 2 (v t)) (hσs : ContDiff ℝ 2 (σ t))
    (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (hv₁ : ∀ x, HasFDerivAt (v t) (v₁ x) x)
    (hv₂ : ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ)
    (hs : ∀ y, s y = ∇ (σ t) y) (hl : ∀ y, l y = Δ (σ t) y)
    (hmod : ∀ r y z, v r (y, z) = u r (y, z + c * r + σ r y) - φ z)
    (y : ℝ^m) (z : ℝ)
    (hv : DifferentiableAt ℝ (fun tx : ℝ × (ℝ^m × ℝ) ↦ v tx.1 tx.2) (t, y, z))
    (hphase : HasDerivAt (fun r ↦ σ r y)
      (d_perp D φ ψ * Δ (σ t) y + (c / 2) * ‖∇ (σ t) y‖ ^ 2 - g y) t)
    (hrde : ∀ w, deriv (fun r ↦ u r (y, w)) t =
      D (splitLaplacian (u t) (y, w)) + f (u t (y, w))) :
    deriv (fun r ↦ v r (y, z)) t =
      (D (splitLaplacian (v t) (y, z)) + c • v₁ (y, z) (0, 1) +
        fderiv ℝ f (φ z) (v t (y, z))) +
      l y • (d_perp D φ ψ • deriv φ z - D (deriv φ z)) +
      ‖s y‖ ^ 2 • (D (deriv (deriv φ) z) + (c / 2) • deriv φ z) +
      frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ (v t) v₁ v₂ s l g (y, z) -
      g y • deriv φ z := by
  have hφ : ContDiff ℝ 2 φ :=
    h₂.smooth.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hφd := hφ.differentiable (by norm_num)
  let U : ℝ × (ℝ^m × ℝ) → ℝ^n := fun tx ↦ φ tx.2.2 + v tx.1 tx.2
  have hU : DifferentiableAt ℝ U (t, y, z) :=
    (hφd.comp (differentiable_snd.comp differentiable_snd) (t, y, z)).add hv
  have hUs : ContDiff ℝ 2 (fun x ↦ U (t, x)) := (hφ.comp contDiff_snd).add hvs
  have hurel (r : ℝ) : u r = fun x ↦ U (r, x.1, x.2 - c * r - σ r x.1) := by
    funext x
    have heval : x.2 - c * r - σ r x.1 + c * r + σ r x.1 = x.2 := by ring
    have h := hmod r x.1 (x.2 - c * r - σ r x.1)
    rw [heval] at h
    dsimp [U]
    rw [h]
    abel
  have hpde := inverseModulated_rde_forced U σ f D c (d_perp D φ ψ) t hUs hσs
    y z _ (g y) hphase hU rfl (by simpa only [hurel] using hrde)
  have htime : deriv (fun r ↦ U (r, y, z)) t = deriv (fun r ↦ v r (y, z)) t := by
    exact deriv_const_add (φ z)
  have hz (w : ℝ) : deriv (fun r ↦ v t (y, r)) w = v₁ (y, w) (0, 1) :=
    (BUC.hasDerivAt_longitudinalDerivativeField (v t) v₁ hv₁ y w).deriv
  have hzz : deriv (deriv (fun r ↦ v t (y, r))) z = v₂ (y, z) (0, 1) (0, 1) := by
    rw [show deriv (fun r ↦ v t (y, r)) = fun w ↦ v₁ (y, w) (0, 1) from funext hz]
    simpa only [BUC.longitudinalDerivativeField_apply, BUC.longitudinalSecondDerivativeField_apply] using
      (BUC.hasDerivAt_longitudinalSecondDerivativeField v₁ v₂ hv₂ y z).deriv
  have hdv : fderiv ℝ (v t) = fun x ↦ v₁ x := funext fun x ↦ (hv₁ x).fderiv
  have hddv : fderiv ℝ (fderiv ℝ (v t)) (y, z) = v₂ (y, z) := by
    rw [hdv]
    exact (hv₂ (y, z)).fderiv
  rw [htime] at hpde
  dsimp only [U] at hpde
  rw [splitLaplacian_profile_add φ hφ (v t) hvs,
    deriv_longitudinal_profile_add φ hφd (v t) (hvs.differentiable (by norm_num)),
    secondDeriv_longitudinal_profile_add φ hφ (v t) hvs,
    mixed_fderiv_profile_add φ hφ (v t) hvs, hddv, hzz, hz] at hpde
  have hode : D (deriv (deriv φ) z) + c • deriv φ z + f (φ z) = 0 := by
    simpa only [InnerProductSpace.laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ,
      iteratedDeriv_zero] using h₂.ode z
  rw [hpde, frontInverseModulationNonlinearity_apply]
  simp only [hs, hl, map_add, smul_add, smul_sub]
  abel_nf at hode ⊢
  rw [eq_neg_of_add_eq_zero_left hode]
  abel

/-- The perturbation equation starting from the unchanged challenge's
`IsRDESolution` predicate in full Euclidean coordinates. Spatial and phase
jets are regularity data for the chosen modulation, not extra assumptions
on the front or the spectral problem. -/
theorem frontInverseModulatedPerturbation_pde_of_solution
    {d : ℕ} (hd : 2 ≤ d) (u : ℝ → ℝ^d → ℝ^n) (hu : IsRDESolution f D u)
    (v : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (σ : ℝ → ℝ^(d - 1) → ℝ) (t : ℝ) (ht : 0 < t)
    (hvs : ContDiff ℝ 2 (v t)) (hσs : ContDiff ℝ 2 (σ t))
    (v₁ : BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
    (v₂ : BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
    (hv₁ : ∀ x, HasFDerivAt (v t) (v₁ x) x)
    (hv₂ : ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (s : BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l g : BUC (ℝ^(d - 1)) ℝ)
    (hs : ∀ y, s y = ∇ (σ t) y) (hl : ∀ y, l y = Δ (σ t) y)
    (hmod : ∀ r y z, v r (y, z) = u r (full y (z + c * r + σ r y)) - φ z)
    (y : ℝ^(d - 1)) (z : ℝ)
    (hv : DifferentiableAt ℝ (fun tx : ℝ × (ℝ^(d - 1) × ℝ) ↦ v tx.1 tx.2) (t, y, z))
    (hphase : HasDerivAt (fun r ↦ σ r y)
      (d_perp D φ ψ * Δ (σ t) y + (c / 2) * ‖∇ (σ t) y‖ ^ 2 - g y) t) :
    deriv (fun r ↦ v r (y, z)) t =
      (D (splitLaplacian (v t) (y, z)) + c • v₁ (y, z) (0, 1) +
        fderiv ℝ f (φ z) (v t (y, z))) +
      l y • (d_perp D φ ψ • deriv φ z - D (deriv φ z)) +
      ‖s y‖ ^ 2 • (D (deriv (deriv φ) z) + (c / 2) • deriv φ z) +
      frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ (v t) v₁ v₂ s l g (y, z) -
      g y • deriv φ z :=
  frontInverseModulatedPerturbation_pde f D c φ ψ h₁ h₂
    (fun r x ↦ u r (full x.1 x.2)) v σ t hvs hσs v₁ v₂ hv₁ hv₂
    s l g hs hl hmod y z hv hphase (fun w ↦ IsRDESolution.split_pde hd hu ht y w)

end

end Planarwave
