/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.ChallengeInitialPhase
import Planarwave.Analysis.ColeHopfEvolution
import Planarwave.Analysis.ColeHopfPDE
import Planarwave.Analysis.HeatJointSmoothReal
import Planarwave.Analysis.HeatSemigroup
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Planarwave.Analysis.HeatJointSmoothMultidimensional

/-!
# Phase evolution for the challenge

The Cole--Hopf construction has the prescribed initial phase and is bounded uniformly continuous
on finite time slabs. Joint positive-time heat smoothness and the heat equation now discharge the
full phase solution predicate in every ambient dimension allowed by the challenge. This file
defines that phase evolution and proves its initial-value and uniform smallness bounds.
The reaction--diffusion construction and nonlinear comparison are handled in other modules.
-/

open Function Set MeasureTheory
open scoped ContDiff Gradient Laplacian InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- The inverse transform of the heat orbit is BUC on every finite time slab. -/
theorem isBUCOn_coleHopfEvolution_slab {d : ℕ} (a β T : ℝ)
    (v : BUC (ℝ^d) ℝ) :
    IsBUCOn (fun p : ℝ × ℝ^d => coleHopfEvolution a β p.1 v p.2)
      (Icc 0 T ×ˢ univ) := by
  refine ⟨uniformContinuousOn_coleHopfEvolution_slab a β T v, ‖v‖, ?_⟩
  intro p _
  exact ((coleHopfEvolution a β p.1 v).norm_apply_le p.2).trans
    (norm_coleHopfEvolution_le a β p.1 v)

/-- Reduction of the classical vHJ solution predicate to classical regularity of the linear
heat orbit of the transformed datum. -/
theorem isVHJSolution_coleHopfEvolution_of_heat {d : ℕ} (a c β : ℝ)
    (v : BUC (ℝ^(d - 1)) ℝ) (hcancel : a * β = c / 2)
    (hsmooth : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ^(d - 1) => heatFlowBUC a p.1 (coleHopfBUC β v) p.2)
      (Ioi 0 ×ˢ univ))
    (hpde : ∀ t > 0, ∀ y, HasDerivAt
      (fun s => heatFlowBUC a s (coleHopfBUC β v) y)
      (a * Δ (fun x => heatFlowBUC a t (coleHopfBUC β v) x) y) t) :
    IsVHJSolution c (fun t y => coleHopfEvolution a β t v y) a := by
  have hdomain : ∀ t y, heatFlowBUC a t (coleHopfBUC β v) y ∈ coleHopfDomain β :=
    fun t y => Icc_coleHopf_subset_domain β ‖v‖
      (heatFlowBUC_coleHopf_mem_Icc a β t v y)
  refine ⟨fun T _ => isBUCOn_coleHopfEvolution_slab a β T v, ?_, ?_⟩
  · exact (contDiffOn_coleHopfInv β).comp hsmooth (fun p _ => hdomain p.1 p.2)
  · intro t ht y
    have hslice : ContDiff ℝ 2 (heatFlowBUC a t (coleHopfBUC β v)) := by
      rw [← contDiffOn_univ]
      have hpair : ContDiff ℝ ∞ (fun y : ℝ^(d - 1) => (t, y)) :=
        contDiff_const.prodMk contDiff_id
      exact (hsmooth.comp hpair.contDiffOn (fun _ _ => ⟨ht, mem_univ _⟩)).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact (hasDerivAt_coleHopfInv_of_heat
      (fun t y => heatFlowBUC a t (coleHopfBUC β v) y) t y a c β
      (hpde t ht y) hslice (hdomain t) hcancel).deriv

/-- The explicit Cole--Hopf phase is a global classical vHJ solution in every dimension. -/
theorem isVHJSolution_coleHopfEvolution {d : ℕ} (a c : ℝ) (ha : 0 < a)
    (v : BUC (ℝ^(d - 1)) ℝ) :
    IsVHJSolution c (fun t y => coleHopfEvolution a (c / (2 * a)) t v y) a := by
  apply isVHJSolution_coleHopfEvolution_of_heat
  · field_simp
  · simpa only [heatFlowBUC_apply] using
      contDiffOn_infty_heatFlow_uncurry ha (coleHopfBUC (c / (2 * a)) v)
  · intro t ht y
    simpa only [heatFlowBUC_apply, smul_eq_mul] using
      hasDerivAt_heatFlow_time ha ht (coleHopfBUC (c / (2 * a)) v) y

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n)

/-- The explicit candidate for the unforced phase in the challenge theorem. -/
def challengePhaseEvolution
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) (t : ℝ) (y : ℝ^(d - 1)) : ℝ :=
  coleHopfEvolution (d_perp D φ ψ) (c / (2 * d_perp D φ ψ)) t
    (initialPhaseBUC f D c φ ψ hd h₂ h₃ hu₀) y

/-- The explicit candidate attains exactly the challenge's prescribed initial phase. -/
@[simp]
theorem challengePhaseEvolution_zero
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) (y : ℝ^(d - 1)) :
    challengePhaseEvolution f D c φ ψ hd h₂ h₃ hu₀ 0 y =
      ∫ z : ℝ, ⟪ψ z, φ z - u₀ (full y z)⟫_ℝ := by
  simp [challengePhaseEvolution]

/-- The challenge's initial smallness bound propagates to the phase for all times. -/
theorem norm_challengePhaseEvolution_le
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) {ε : ℝ}
    (hclose : IsCloseToFront φ u₀ ε) (t : ℝ) (y : ℝ^(d - 1)) :
    ‖challengePhaseEvolution f D c φ ψ hd h₂ h₃ hu₀ t y‖ ≤
      ε * ∫ z : ℝ, ‖ψ z‖ := by
  exact ((coleHopfEvolution _ _ t _).norm_apply_le y).trans
    ((norm_coleHopfEvolution_le _ _ t _).trans
      (norm_initialPhaseBUC_le f D c φ ψ hd h₂ h₃ hu₀ hclose))

/-- The challenge's prescribed unforced phase is a global classical solution for every
`d ≥ 2`, with no additional heat regularity assumptions. -/
theorem isVHJSolution_challengePhaseEvolution
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) :
    IsVHJSolution c (challengePhaseEvolution f D c φ ψ hd h₂ h₃ hu₀)
      (d_perp D φ ψ) :=
  isVHJSolution_coleHopfEvolution (d := d) _ c h₃.transverse_low_wavenumber _

end

end Planarwave
