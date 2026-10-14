/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
module

public import Mathlib
public import Planarwave.Statement
public import Planarwave.Proof

@[expose] public section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-!
# Stability of planar fronts in reaction diffusion systems.

This file contains a formalization of the statement that the dynamics near a spectrally stable
planar front in a reaction-diffusion equation are described by a viscous Hamilton-Jacobi equation.

The main theorem is `vHJ_approximates_planar_front`, which corresponds to Theorem 1.6 in [1] (with the uniqueness of
the solutions omitted).

* [1]. B. de Rijk and J. van Winden, "Stability and dynamics of planar fronts in reaction-diffusion systems under
  nonlocalized perturbations.", arXiv.2601.05832.
-/

open Set Planarwave Set InnerProductSpace

-- PDE data: dimension, nonlinearity, diffusion matrix.
variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
-- Front data: speed, profile, transverse diffusion coefficient
variable (c : ℝ) (φ : ℝ → ℝ^n) (ψ : ℝ → ℝ^n)
-- Prospective solutions to the relevant PDEs.
variable (u : ℝ → ℝ^d → ℝ^n) (σ : ℝ → ℝ^(d - 1) → ℝ)

/-- A solution to the RDE which starts close to a planar front is well-approximated by the front
shifted according to a viscous Hamilton-Jacobi equation.
-/
theorem vHJ_approximates_planar_front
  (hn : 1 ≤ n) (hd : 2 ≤ d)
  (h₁ : IsSmoothParabolic f D)
  (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
  ∃ C > 0, ∃ ε > 0, ∀ E_0 ∈ Icc 0 ε, ∀ u₀ : ℝ^d → ℝ^n, IsBUC u₀ → IsCloseToFront φ u₀ E_0 →
    ∃ u σ, IsRDESolution f D u ∧ IsVHJSolution c σ (d_perp D φ ψ) ∧
      u 0 = u₀ ∧ (∀ y, σ 0 y = ∫ z, ⟪ψ z, φ z - u 0 (full y z)⟫_ℝ) ∧
      ∀ t ≥ 0, ∀ x, ‖u t x - φ (horizontal x - c * t - σ t (transverse x))‖ ≤
        C * E_0 * (E_0 + (1 + t)⁻¹ * Real.log (2 + t)) :=
  Planarwave.vHJ_approximates_planar_front_solution

end
