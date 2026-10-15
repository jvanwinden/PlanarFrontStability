/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
module

public import Mathlib

@[expose] public section

namespace Planarwave

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-!
# Solution-side statement definitions

These internal declarations mirror the protected `Challenge.lean`, without
its admitted main theorem. They live in `Planarwave` so that `Solution.lean`
can repeat the challenge's public declarations without name collisions.

The analytic library imports this module, never `Challenge`. `Planarwave.Proof`
transfers the completed proof to the copied predicates in `Solution.lean`.
-/

open scoped Gradient Laplacian EuclideanGeometry Topology InnerProductSpace ContDiff
open Filter Function Set MeasureTheory

-- PDE data: dimension, nonlinearity, diffusion matrix.
variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
-- Front data: speed, profile, transverse diffusion coefficient
variable (c : ℝ) (φ : ℝ → ℝ^n) (ψ : ℝ → ℝ^n)
-- Prospective solutions to the relevant PDEs.
variable (u : ℝ → ℝ^d → ℝ^n) (σ : ℝ → ℝ^(d - 1) → ℝ)

section PDESetup

def IsBUCOn {α β : Type*} [UniformSpace α] [UniformSpace β] [Norm β] (f : α → β) (s : Set α) :=
  UniformContinuousOn f s ∧ ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C

def IsBUC {α β : Type*} [UniformSpace α] [UniformSpace β] [Norm β] (f : α → β) := IsBUCOn f univ

/-- The PDE is uniformly parabolic and the nonlinearity is smooth. -/
structure IsSmoothParabolic : Prop where
  smooth : ContDiff ℝ ∞ f
  positive : D.IsPositive
  kernel : Injective D

/-- Define our notion of (global) solution for the reaction-diffusion equation. -/
structure IsRDESolution : Prop where
  cont : ∀ t > 0, IsBUCOn (uncurry u) (Icc 0 t ×ˢ univ)
  smooth : ContDiffOn ℝ ∞ (uncurry u) (Ioi 0 ×ˢ univ)
  pde : ∀ t > 0, ∀ x, deriv (u · x) t = D (Δ (u t ·) x) + f (u t x)

noncomputable def d_perp : ℝ := ∫ x, ⟪ψ x, D (deriv φ x)⟫_ℝ

/-- Define our notion of (global) solution for the viscous Hamilton-Jacobi equation. -/
structure IsVHJSolution (d_perp : ℝ) : Prop where
  cont : ∀ t > 0, IsBUCOn (uncurry σ) (Icc 0 t ×ˢ univ)
  smooth : ContDiffOn ℝ ∞ (uncurry σ) (Ioi 0 ×ˢ univ)
  pde : ∀ t > 0, ∀ y, deriv (σ · y) t = d_perp * (Δ (σ t ·) y) + (c / 2) * ‖∇ (σ t ·) y‖^2

end PDESetup

/-- The front is twice continuously differentiable, has left and right limits, and satisfies the
traveling wave ODE. -/
structure IsSmoothFront : Prop where
  smooth : ContDiff ℝ ∞ φ
  ode : ∀ z, D (Δ φ z) + c • deriv φ z + f (φ z) = 0
  endpoints : ∃ φ₁ φ₂, Tendsto φ atBot (𝓝 φ₁) ∧ Tendsto φ atTop (𝓝 φ₂)

public section SpectralStability

/-- Complexify a map from ℝ^n → ℝ^n. -/
noncomputable def ContinuousLinearMap.complexify (L : ℝ^n →L[ℝ] ℝ^n) :=
  Matrix.toEuclideanLin.symm L.toLinearMap|>.map (fun x ↦ (x : ℂ))|>.toEuclideanLin

/-- Embed ℝ^n into ℂ^n in the natural way. -/
noncomputable def embed (x : ℝ^n) : ℂ^n := .toLp 2 fun i ↦ ↑(x i)

/-- Define our notion of solution to the resolvent equation at transverse wavenumber k. -/
structure IsTransverseResolventSolution (k : ℝ) (l : ℂ) (v w : ℝ → ℂ^n) : Prop where
  /-- v is twice continuously differentiable. -/
  smooth : ContDiff ℝ 2 v
  /-- The first two derivatives of v are bounded uniformly continuous. -/
  buc : ∀ i ≤ 2, IsBUC (iteratedDeriv i (v ·))
  /-- v satisfies the resolvent equation. -/
  pde : ∀ z, ((ContinuousLinearMap.complexify D)) ((Δ v z) - (k ^ 2) • (v z)) +
    c • (deriv v z) + (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) (v z) - l • v z = w z

def TransverseSpectrum (k : ℝ) : Set ℂ :=
  compl {l | ∀ w, IsBUC w → ∃! v, IsTransverseResolventSolution f D c φ k l v w}

structure IsSpectrallyStableWithAdjoint : Prop where
  /-- Integrability of the adjoint eigenfunction. -/
  integrable : Integrable ψ
  /-- Normalization of the adjoint eigenfunction. -/
  normalized : ∫ x, ⟪ψ x, deriv φ x⟫_ℝ = 1
  /-- L₀ has a spectral gap. -/
  horizontal_spectral_gap : ∃ θ > 0, ∀ l ∈ TransverseSpectrum f D c φ 0, l = 0 ∨ l.re ≤ -θ
  /-- L₀ v = 0 iff v is a multiple of φ'. -/
  horizontal_kernel : ∀ v, IsTransverseResolventSolution f D c φ 0 0 v 0 ↔
    ∃ c : ℂ, ∀ x, v x = c • embed (deriv φ x)
  /-- L₀ v = w has a solution iff w is orthogonal to ψ. -/
  horizontal_solvability : ∀ w, IsBUC w →
    (∫ z, ⟪embed (ψ z), w z⟫_ℂ = 0 ↔ ∃ v, IsTransverseResolventSolution f D c φ 0 0 v w)
  /-- Transverse spectral stability for small wavenumbers. -/
  transverse_low_wavenumber : d_perp D φ ψ > 0
  /-- Transverse spectral stability for medium-high wavenumbers. -/
  transverse_high_wavenumber : ∀ k₀ > 0, ∃ θ₁ > 0,
    ∀ k ≥ k₀, ∀ l ∈ TransverseSpectrum f D c φ k, l.re ≤ -θ₁

end SpectralStability

section NonlinearStability

/-- Extract the horizontal coordinate from x. -/
noncomputable def horizontal (x : ℝ^d) : ℝ := if hd : 1 ≤ d then x ⟨d - 1, by omega⟩ else 0

/-- Extract the transverse coordinates from x. -/
def transverse (x : ℝ^d) : ℝ^(d - 1) := .toLp 2 (fun i ↦ x (Fin.castLE (by simp only [tsub_le_iff_right,
  le_add_iff_nonneg_right, zero_le]) i))

/-- Assemble the full coordinate x from y and z. -/
def full (y : ℝ^(d - 1)) (z : ℝ) : ℝ^d :=
  .toLp 2 (fun i ↦ if h : i < d - 1 then y ⟨i, h⟩ else z)

/-- Define closeness to the front. -/
def IsCloseToFront (u : ℝ^d → ℝ^n) (ε : ℝ) : Prop := ∀ x, ‖u x - φ (horizontal x)‖ ≤ ε

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
  sorry

end NonlinearStability

end Planarwave
