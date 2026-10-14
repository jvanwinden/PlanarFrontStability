/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontModulationPDE
import all Planarwave.Analysis.FrontModulationSource
import all Planarwave.Analysis.FrontSpatialGenerator
import all Planarwave.Analysis.MatrixReactionDiffusionLocalClassical
import all Planarwave.Analysis.MatrixReactionDiffusionPositiveJets

/-!
# The tracking equation on the physical solution's interval of existence

The modulation calculation needs only a finite-slab mild physical solution,
not global existence. Derive the split physical PDE on its actual interval,
and identify the perturbation's time derivative with the exact bundled source
used in the tracking estimates.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

include hd in
/-- The original matrix mild solution satisfies the physical PDE in split
coordinates, strictly inside its finite interval of existence. -/
theorem IsMatrixReactionDiffusionMildOn.split_pde
    {T : ℝ} {u : ℝ → BUC (ℝ^d) (ℝ^n)} (hT : 0 ≤ T)
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hu : ContinuousOn u (Icc 0 T)) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (y : ℝ^(d - 1)) (z : ℝ) :
    deriv (fun r ↦ u r (full y z)) t =
      D (splitLaplacian (fun x ↦ u t (full x.1 x.2)) (y, z)) + f (u t (full y z)) := by
  rw [(hm.hasDerivAt_of_continuousOn h₁ hT hu ht (full y z)).deriv,
    laplacian_eq_splitLaplacian hd _ ((hm.spatialRegularOn_Ioo h₁ hT hu 2).contDiff ht)]

include hd in
/-- The paper's perturbation equation with an actual time derivative and
the full BUC source. The physical solution is only assumed to exist on
the finite interval used here. -/
theorem hasDerivAt_front_modulation_of_mild
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Ioo 0 T)
    (u : ℝ → BUC (ℝ^d) (ℝ^n)) (hu : ContinuousOn u (Icc 0 T))
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (v : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (σ : ℝ → BUC (ℝ^(d - 1)) ℝ)
    (v₁ : BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
    (v₂ : BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
    (hv₁ : ∀ x, HasFDerivAt (v t) (v₁ x) x)
    (hv₂ : ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (hσs : ContDiff ℝ 2 (σ t))
    (s : BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l g : BUC (ℝ^(d - 1)) ℝ)
    (hs : ∀ y, s y = ∇ (σ t : ℝ^(d - 1) → ℝ) y)
    (hl : ∀ y, l y = Δ (σ t : ℝ^(d - 1) → ℝ) y)
    (hmod : ∀ r y z, v r (y, z) = u r (full y (z + c * r + σ r y)) - φ z)
    (y : ℝ^(d - 1)) (z : ℝ)
    (hv : DifferentiableAt ℝ (fun tx : ℝ × (ℝ^(d - 1) × ℝ) ↦ v tx.1 tx.2) (t, y, z))
    (hphase : HasDerivAt (fun r ↦ σ r y)
      (d_perp D φ ψ * l y + (c / 2) * ‖s y‖ ^ 2 - g y) t) :
    HasDerivAt (fun r ↦ v r (y, z))
      (D (splitLaplacian (v t) (y, z)) + c • fderiv ℝ (v t) (y, z) (0, 1) +
        fderiv ℝ f (φ z) (v t (y, z)) +
        frontModulationSource f D c φ ψ h₃
          (frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ (v t) v₁ v₂ s l g)
          s l g (y, z)) t := by
  have hvs := contDiff_two_of_buc_fderivatives (v t) v₁ v₂ hv₁ hv₂
  have hp := frontInverseModulatedPerturbation_pde f D c φ ψ h₁ h₂
    (fun r x ↦ u r (full x.1 x.2)) v (fun r ↦ σ r) t hvs hσs
    v₁ v₂ hv₁ hv₂ s l g hs hl hmod y z hv
    (by simpa only [hs, hl] using hphase)
    (fun w ↦ hm.split_pde f D h₁ hd hT hu ht y w)
  have hline : DifferentiableAt ℝ (fun r : ℝ ↦ (r, (y, z))) t :=
    differentiableAt_id.prodMk (differentiableAt_const (y, z))
  have hdtime : DifferentiableAt ℝ (fun r ↦ v r (y, z)) t := by
    simpa only [Function.comp_def] using! hv.comp t hline
  have htderiv := hdtime.hasDerivAt
  rw [hp] at htderiv
  convert! htderiv using 1
  rw [(hv₁ (y, z)).fderiv,
    frontModulationSource_apply]
  abel

end

end Planarwave
