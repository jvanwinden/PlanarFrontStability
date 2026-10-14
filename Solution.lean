/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Statement
import all Planarwave.Analysis.FrontTrackingGlobal
import all Planarwave.Analysis.FrontTrackingVHJComparison
import Batteries.Tactic.Alias

/-!
# Solution for the planar-front comparator challenge

The public theorem `vHJ_approximates_planar_front` has the name and statement
required by `comparator.json`. Its proof follows the paper's spectral
estimates, causal tracking construction, nonlinear bootstrap, maximal
continuation, and forced/unforced phase comparison.

This module and its dependencies do not import `Challenge`: the solution-side
definitions come from `Planarwave.Statement`. This keeps the reference's
admitted theorem out of the solution environment. Compare the two modules
using the external comparator and `comparator.json`, not by importing both.
-/

open scoped Gradient Laplacian EuclideanGeometry Topology InnerProductSpace ContDiff
open Filter Function Set MeasureTheory
open Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
  (c : ℝ) (φ ψ : ℝ → ℝ^n)

/-- The complete challenge statement, proved without importing the reference theorem. -/
public theorem vHJ_approximates_planar_front
  (hn : 1 ≤ n) (hd : 2 ≤ d)
  (h₁ : IsSmoothParabolic f D)
  (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
  ∃ C > 0, ∃ ε > 0, ∀ E_0 ∈ Icc 0 ε, ∀ u₀ : ℝ^d → ℝ^n, IsBUC u₀ → IsCloseToFront φ u₀ E_0 →
    ∃ u σ, IsRDESolution f D u ∧ IsVHJSolution c σ (d_perp D φ ψ) ∧
      u 0 = u₀ ∧ (∀ y, σ 0 y = ∫ z, ⟪ψ z, φ z - u 0 (full y z)⟫_ℝ) ∧
      ∀ t ≥ 0, ∀ x, ‖u t x - φ (horizontal x - c * t - σ t (transverse x))‖ ≤
        C * E_0 * (E_0 + (1 + t)⁻¹ * Real.log (2 + t)) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : Nontrivial (ℝ^n) := inferInstance
  obtain ⟨_, _, εg, hεg, hglobal⟩ :=
    exists_front_global_solution_with_tracking f D c φ ψ h₁ h₂ h₃ hd
  obtain ⟨C, hC, εv, hεv, hcompare⟩ :=
    exists_front_tracking_vHJ_error_bound f D c φ ψ h₁ h₂ h₃ hd
  refine ⟨C, hC, min εg εv, lt_min hεg hεv, ?_⟩
  intro M hM u₀ hu₀ hclose
  let u₀b := BUC.ofIsBUC hu₀
  let v₀ := frontInverseModulatedPerturbation f D c φ h₂ hd u₀b 0 0
  have hcloseb : IsCloseToFront φ (u₀b : ℝ^d → ℝ^n) M := hclose
  have hv₀ : ‖v₀‖ ≤ M :=
    (norm_frontInverseModulatedPerturbation_zero_le_iff f D c φ h₂ hd u₀b hM.1).mpr hcloseb
  obtain ⟨u, hinit, hu, _, htracking⟩ :=
    hglobal u₀b v₀ M hM.1 (hM.2.trans (min_le_left _ _)) hv₀
      (by simp only [mul_zero]; rfl)
  refine ⟨(fun t x ↦ u t x),
    challengePhaseEvolution f D c φ ψ hd h₂ h₃ (isBUC_coe u₀b), hu,
    isVHJSolution_challengePhaseEvolution f D c φ ψ hd h₂ h₃ (isBUC_coe u₀b), ?_, ?_, ?_⟩
  · funext x
    change u 0 x = u₀ x
    rw [hinit]
    rfl
  · intro y
    simpa only [hinit] using
      challengePhaseEvolution_zero f D c φ ψ hd h₂ h₃ (isBUC_coe u₀b) y
  · intro t ht x
    obtain ⟨X, hXu, _, _⟩ := htracking t ht
    have hXinit : X.u 0 = u₀b := by rw [hXu, hinit]
    simpa only [hXu] using hcompare X u₀b hXinit
      ⟨hM.1, hM.2.trans (min_le_right _ _)⟩ hcloseb t ⟨ht, le_rfl⟩ x

end

namespace Planarwave

/-- Compatibility name for the previously namespaced solution theorem. -/
alias vHJ_approximates_planar_front_proved := _root_.vHJ_approximates_planar_front

end Planarwave
