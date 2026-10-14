/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontProfileHigherBounds
import all Planarwave.Analysis.MatrixReactionDiffusionPositiveJets
import Planarwave.Analysis.ModulationSpatialRegularity
import Planarwave.Analysis.BUCSpatialRegularityLocal

/-!
# Time-continuous jets of the physical inverse modulation

Transfer the physical trajectory to split coordinates and then to the
moving phase coordinates. The continuity statement includes time zero
and needs no spatial derivatives; the higher-order statement transfers
the actual time-continuous spatial jets without an extra derivative.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ}
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ : ℝ → ℝ^n)
  (h₂ : IsSmoothFront f D c φ) (hd : 2 ≤ d)

/-- The actual inverse-modulated perturbation is continuous in the spatial
supremum norm, even at the rough initial datum. -/
theorem continuousOn_frontInverseModulatedPerturbation
    {s : Set ℝ} {u : ℝ → BUC (ℝ^d) (ℝ^n)}
    {a : ℝ → ℝ} {σ : ℝ → BUC (ℝ^(d - 1)) ℝ}
    (hu : ContinuousOn u s) (ha : ContinuousOn a s) (hσ : ContinuousOn σ s) :
    ContinuousOn (fun t ↦ frontInverseModulatedPerturbation f D c φ h₂ hd
      (u t) (a t) (σ t)) s := by
  let L := (coordinateEquiv hd).symm.toContinuousLinearMap
  have hp := (BUC.compCLM (𝕜 := ℝ) L L.uniformContinuous).continuous.comp_continuousOn hu
  exact (continuousOn_modulationShift ha hσ hp).sub continuousOn_const

variable [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n)
  (h₁ : IsSmoothParabolic f D) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₁ h₃ in
/-- The physical inverse-modulation map preserves every finite hierarchy
of BUC jets. The fixed profile's jets follow from the front ODE. -/
theorem spatialRegularOn_frontInverseModulatedPerturbation
    {s : Set ℝ} {k : ℕ} {u : ℝ → BUC (ℝ^d) (ℝ^n)}
    {a : ℝ → ℝ} {σ : ℝ → BUC (ℝ^(d - 1)) ℝ}
    (hu : BUCSpatialRegularOn s k u) (ha : ContinuousOn a s)
    (hσ : BUCSpatialRegularOn s k σ) :
    BUCSpatialRegularOn s k (fun t ↦ frontInverseModulatedPerturbation f D c φ h₂ hd
      (u t) (a t) (σ t)) := by
  obtain ⟨P, hP, hp⟩ := exists_frontSplitProfile_cn_bound
    (m := d - 1) f D c φ ψ h₁ h₂ h₃ k
  have hshift := (hu.precompCLM (coordinateEquiv hd).symm.toContinuousLinearMap).modulationShift hσ ha
  simpa only [sub_eq_add_neg] using!
    hshift.add (hp.regularOn_const s).neg

include h₁ h₃ in
/-- Positive-time jets of the actual inverse-modulated mild solution.
No physical derivative or physical norm bound is supplied as an input:
compactness and parabolic smoothing construct those jets. -/
theorem spatialRegularOn_frontInverseModulatedPerturbation_of_mild
    {T : ℝ} {u : ℝ → BUC (ℝ^d) (ℝ^n)}
    {σ : ℝ → BUC (ℝ^(d - 1)) ℝ} {k : ℕ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T))
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hσ : BUCSpatialRegularOn (Ioo 0 T) k σ) :
    BUCSpatialRegularOn (Ioo 0 T) k
      (fun t ↦ frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)) := by
  exact spatialRegularOn_frontInverseModulatedPerturbation f D c φ h₂ hd ψ h₁ h₃
    (hm.spatialRegularOn_Ioo h₁ hT hu k) (by fun_prop) hσ

end

end Planarwave
