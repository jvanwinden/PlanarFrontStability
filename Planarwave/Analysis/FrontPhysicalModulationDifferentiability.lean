/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearity
import all Planarwave.Analysis.MatrixReactionDiffusionLocalClassical
import Planarwave.Analysis.BUCSpacetimeCalculus
import Planarwave.Analysis.BUCSpatialRegularity

/-!
# Joint differentiability of the physical inverse modulation

At positive interior times parabolic smoothing makes the physical solution
jointly smooth. Composing with the actual phase-dependent coordinate change
then gives the joint differentiability required by the modulation chain rule.
The phase's joint regularity can itself be recovered from its genuine BUC
spatial jet and its continuous pointwise time derivative.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₂ : IsSmoothFront f D c φ) (hd : 2 ≤ d)

/-- Joint differentiability passes through the paper's inverse-modulation
Ansatz, with no independent differentiability hypothesis on the perturbation. -/
theorem differentiableAt_frontInverseModulatedPerturbation
    (u : ℝ → BUC (ℝ^d) (ℝ^n)) (σ : ℝ → BUC (ℝ^(d - 1)) ℝ)
    (t : ℝ) (y : ℝ^(d - 1)) (z : ℝ)
    (hu : DifferentiableAt ℝ (fun p : ℝ × ℝ^d ↦ u p.1 p.2)
      (t, full y (z + c * t + σ t y)))
    (hσ : DifferentiableAt ℝ (fun p : ℝ × ℝ^(d - 1) ↦ σ p.1 p.2) (t, y)) :
    DifferentiableAt ℝ
      (fun p : ℝ × (ℝ^(d - 1) × ℝ) ↦
        frontInverseModulatedPerturbation f D c φ h₂ hd (u p.1) (c * p.1) (σ p.1) p.2)
      (t, y, z) := by
  have ht : DifferentiableAt ℝ (fun p : ℝ × (ℝ^(d - 1) × ℝ) ↦ p.1) (t, y, z) :=
    differentiableAt_fst
  have hy : DifferentiableAt ℝ (fun p : ℝ × (ℝ^(d - 1) × ℝ) ↦ p.2.1) (t, y, z) :=
    differentiableAt_fst.comp _ differentiableAt_snd
  have hz : DifferentiableAt ℝ (fun p : ℝ × (ℝ^(d - 1) × ℝ) ↦ p.2.2) (t, y, z) :=
    differentiableAt_snd.comp _ differentiableAt_snd
  have hs := hσ.comp (t, y, z) (ht.prodMk hy)
  have hshift := hz.add ((differentiableAt_const c).mul ht) |>.add hs
  have hx := (coordinateEquiv hd).symm.differentiableAt.comp (t, y, z)
    (hy.prodMk hshift)
  have hφ : Differentiable ℝ φ := h₂.smooth.differentiable (by simp)
  exact (hu.comp (t, y, z) (ht.prodMk hx)).sub (hφ.differentiableAt.comp _ hz)

/-- Positive-time parabolic smoothing supplies the physical factor in the
inverse-modulation chain rule on any finite continuous mild-solution slab. -/
theorem differentiableAt_frontInverseModulatedPerturbation_of_mild
    [Nontrivial (ℝ^n)] (h₁ : IsSmoothParabolic f D)
    {T : ℝ} {u : ℝ → BUC (ℝ^d) (ℝ^n)} {σ : ℝ → BUC (ℝ^(d - 1)) ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T))
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (y : ℝ^(d - 1)) (z : ℝ)
    (hσ : DifferentiableAt ℝ (fun p : ℝ × ℝ^(d - 1) ↦ σ p.1 p.2) (t, y)) :
    DifferentiableAt ℝ
      (fun p : ℝ × (ℝ^(d - 1) × ℝ) ↦
        frontInverseModulatedPerturbation f D c φ h₂ hd (u p.1) (c * p.1) (σ p.1) p.2)
      (t, y, z) := by
  apply differentiableAt_frontInverseModulatedPerturbation f D c φ h₂ hd u σ t y z
  · exact ((hm.contDiffOn_infty_of_continuousOn h₁ hT hu).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt
        (by simp)
  · exact hσ

/-- A continuous BUC time derivative and a genuine continuous BUC spatial
jet give joint `C¹` regularity of a phase (or any other BUC trajectory). -/
theorem BUCSpatialRegularOn.contDiffOn_one_of_pointwise_hasDerivAt
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set ℝ} (hs : IsOpen s) {σ v : ℝ → BUC E F}
    (hσ : BUCSpatialRegularOn s 1 σ) (hv : ContinuousOn v s)
    (htime : ∀ t ∈ s, ∀ x, HasDerivAt (fun r ↦ σ r x) (v t x) t) :
    ContDiffOn ℝ 1 (fun p : ℝ × E ↦ σ p.1 p.2) (s ×ˢ univ) := by
  obtain ⟨_, q, hq, hdq⟩ := hσ
  exact contDiffOn_one_buc_spacetime hs hv hq htime hdq

/-- The forced phase equation supplies a continuous BUC time derivative
from its gradient, Laplacian, and forcing fields. Thus the already constructed
phase is jointly `C¹`, rather than merely differentiable along separate lines. -/
theorem contDiffOn_one_forced_phase_of_buc_fields
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a c : ℝ) {I : Set ℝ} (hI : IsOpen I)
    {σ l g : ℝ → BUC E ℝ} {s : ℝ → BUC E E}
    (hσ : BUCSpatialRegularOn I 1 σ)
    (hs : ContinuousOn s I) (hl : ContinuousOn l I) (hg : ContinuousOn g I)
    (hgrad : ∀ t ∈ I, ∀ y, s t y = ∇ (σ t : E → ℝ) y)
    (hlap : ∀ t ∈ I, ∀ y, l t y = Δ (σ t : E → ℝ) y)
    (hphase : ∀ t ∈ I, ∀ y, HasDerivAt (fun r ↦ σ r y)
      (a * Δ (σ t : E → ℝ) y + (c / 2) * ‖∇ (σ t : E → ℝ) y‖ ^ 2 - g t y) t) :
    ContDiffOn ℝ 1 (fun p : ℝ × E ↦ σ p.1 p.2) (I ×ˢ univ) := by
  have hsq : ContinuousOn (fun t ↦ phaseGradientSquared (s t)) I :=
    (BUC.continuous_bilinearBUC (innerSL ℝ)).comp_continuousOn (hs.prodMk hs)
  apply BUCSpatialRegularOn.contDiffOn_one_of_pointwise_hasDerivAt hI hσ
    ((hl.const_smul a).add (hsq.const_smul (c / 2)) |>.sub hg)
  intro t ht y
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    BUC.sub_apply, BUC.add_apply, BUC.smul_apply,
    phaseGradientSquared_apply, smul_eq_mul, hgrad t ht y, hlap t ht y]
    using hphase t ht y

end

end Planarwave
