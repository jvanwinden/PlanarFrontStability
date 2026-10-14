/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontPhysicalModulationPDE
import all Planarwave.Analysis.FrontPhysicalModulationDifferentiability
import all Planarwave.Analysis.FrontPhysicalModulationRegularity
import all Planarwave.Analysis.FrontSplitClassicalDuhamel

/-!
# Duhamel's formula for the actual inverse-modulated physical solution

This is the identification used in Step 2 of the paper's a priori estimate.
The perturbation is the actual inverse modulation of a finite-slab physical
mild solution. Its spatial jets and joint differentiability are derived by
parabolic smoothing and the forced phase equation. No independent equation
or semigroup identity for that perturbation is assumed.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- The actual inverse-modulated solution equals the full front semigroup
response. The supplied continuous nonlinear source is identified by the
paper's formula with genuine derivatives only at positive interior times. -/
theorem frontInverseModulatedPerturbation_eq_realOrbit_add_duhamel
    {T : ℝ} (hT : 0 ≤ T)
    (u : ℝ → BUC (ℝ^d) (ℝ^n)) (hu : ContinuousOn u (Icc 0 T))
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (σ : ℝ → BUC (ℝ^(d - 1)) ℝ) (hσc : ContinuousOn σ (Icc 0 T))
    (hσreg : BUCSpatialRegularOn (Ioo 0 T) 2 σ)
    (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l g : ℝ → BUC (ℝ^(d - 1)) ℝ)
    (hs : ContinuousOn s (Icc 0 T)) (hl : ContinuousOn l (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (hgrad : ∀ t ∈ Ioo 0 T, ∀ y, s t y = ∇ (σ t : ℝ^(d - 1) → ℝ) y)
    (hlap : ∀ t ∈ Ioo 0 T, ∀ y, l t y = Δ (σ t : ℝ^(d - 1) → ℝ) y)
    (hphase : ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
      (d_perp D φ ψ * l t y + (c / 2) * ‖s t y‖ ^ 2 - g t y) t)
    (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) (hN : ContinuousOn N (Icc 0 T))
    (v₁ : ℝ → BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
    (v₂ : ℝ → BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
    (hv₁ : ∀ t ∈ Ioo 0 T, ∀ x, HasFDerivAt
      (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)) (v₁ t x) x)
    (hv₂ : ∀ t ∈ Ioo 0 T, ∀ x, HasFDerivAt (v₁ t) (v₂ t x) x)
    (hNid : ∀ t ∈ Ioo 0 T, N t = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
      (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t))
      (v₁ t) (v₂ t) (s t) (l t) (g t))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    embedSplitSpatial hd (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)) =
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit
        (embedSplitSpatial hd (frontInverseModulatedPerturbation f D c φ h₂ hd (u 0) (c * 0) (σ 0))) t +
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel
        (fun r ↦ embedSplitSpatial hd (frontModulationSource f D c φ ψ h₃ (N r) (s r) (l r) (g r))) t := by
  let v := fun r ↦ frontInverseModulatedPerturbation f D c φ h₂ hd (u r) (c * r) (σ r)
  have hvc : ContinuousOn v (Icc 0 T) :=
    continuousOn_frontInverseModulatedPerturbation f D c φ h₂ hd hu (by fun_prop) hσc
  have hvr : BUCSpatialRegularOn (Ioo 0 T) 2 v :=
    spatialRegularOn_frontInverseModulatedPerturbation_of_mild f D c φ h₂ hd ψ h₁ h₃ hT hu hm hσreg
  have hσjoint := contDiffOn_one_forced_phase_of_buc_fields (d_perp D φ ψ) c
    isOpen_Ioo hσreg.of_succ (hs.mono Ioo_subset_Icc_self)
    (hl.mono Ioo_subset_Icc_self) (hg.mono Ioo_subset_Icc_self) hgrad hlap
    (fun r hr y ↦ by simpa only [← hgrad r hr y, ← hlap r hr y] using hphase r hr y)
  apply embedSplitSpatial_eq_realOrbit_add_duhamel_of_classical f D c φ h₁ h₂ hd hvc
    (continuousOn_frontModulationSource f D c φ ψ h₃ hN hs hl hg) hvr _ ht
  intro r hr y z
  have hσd : DifferentiableAt ℝ (fun p : ℝ × ℝ^(d - 1) ↦ σ p.1 p.2) (r, y) :=
    (hσjoint.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt
      (by norm_num)
  have hvd := differentiableAt_frontInverseModulatedPerturbation_of_mild
    f D c φ h₂ hd h₁ hT hu hm hr y z hσd
  have hp := hasDerivAt_front_modulation_of_mild f D c φ ψ h₁ h₂ h₃ hd hT hr
    u hu hm v σ (v₁ r) (v₂ r) (hv₁ r hr) (hv₂ r hr) (hσreg.contDiff hr)
    (s r) (l r) (g r) (hgrad r hr) (hlap r hr)
    (fun q y z ↦ frontInverseModulatedPerturbation_apply f D c φ h₂ hd (u q) (c * q) (σ q) y z)
    y z hvd (hphase r hr y)
  simpa only [v, ← hNid r hr] using! hp

end

end Planarwave
