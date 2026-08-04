import Mathlib

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-!
# Stability of planar fronts in reaction diffusion systems.

This file formalizes the statement of Theorem 1.6 from De Rijk and Van Winden, "Stability and dynamics of
planar fronts in reaction-diffusion systems under nonlocalized perturbations.", arXiv.2601.05832.
-/

open EuclideanGeometry ContDiff Laplacian Filter Gradient Set Function MeasureTheory InnerProductSpace

-- PDE data: dimension, nonlinearity, diffusion matrix.
variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
-- Front data: speed, profile, transverse diffusion coefficient
variable (c : ℝ) (φ : ℝ → ℝ^n) (ψ : ℝ → ℝ^n)
-- Prospective solutions to the relevant PDEs.
variable (u : ℝ → ℝ^d → ℝ^n) (σ : ℝ → ℝ^(d - 1) → ℝ)

section PDESetup

/-- The PDE is uniformly parabolic and the nonlinearity is smooth. -/
structure IsSmoothParabolic : Prop where
  smooth : ContDiff ℝ ∞ f
  positive : D.IsPositive
  kernel : Injective D

/-- Define our notion of (local) solution for the reaction-diffusion equation. -/
structure IsSmoothLocalRDESolution (t : ℝ) : Prop where
  cont : UniformContinuousOn (uncurry u) (Icc 0 t ×ˢ univ)
  smooth : ContDiffOn ℝ ∞ (uncurry u) (Ioc 0 t ×ˢ univ)
  pde : ∀ s ∈ Ioc 0 t, ∀ x, deriv (u · x) s = D (Δ (u s ·) x) + f (u s x)

noncomputable def d_perp : ℝ := ∫ x, ⟪ψ x, D (deriv φ x)⟫_ℝ

/-- Define our notion of (global) solution for the viscous Hamilton-Jacobi equation. -/
structure IsVHJSolution (d_perp : ℝ) : Prop where
  cont : ∀ s > 0, UniformContinuousOn (Function.uncurry σ) (Icc 0 s ×ˢ univ)
  smooth : ContDiffOn ℝ ∞ (Function.uncurry σ) (Ioi 0 ×ˢ univ)
  pde : ∀ t > 0, ∀ y, deriv (σ · y) t = c + d_perp * (Δ (σ t ·) y) + ((c ^ 2) / 2) * ‖∇ (σ t ·) y‖^2

end PDESetup

/-- The front is twice continuously differentiable, has left and right limits, and satisfies the
traveling wave ODE. -/
structure IsSmoothFront : Prop where
  smooth : ContDiff ℝ 2 φ
  ode : ∀ x, D (Δ φ x) + c • deriv φ x + f (φ x) = 0
  left_endpoint : ∃ φ₁, Tendsto φ atBot φ₁
  right_endpoint : ∃ φ₂, Tendsto φ atTop φ₂

section SpectralStability

/-- Complexify a map from ℝ^n → ℝ^n. -/
noncomputable def ContinuousLinearMap.complexify (L : ℝ^n →L[ℝ] ℝ^n) :=
  Matrix.toEuclideanLin.symm L.toLinearMap|>.map (fun x ↦ (x : ℂ))|>.toEuclideanLin

/-- Embed ℝ^n into ℂ^n in the natural way. -/
noncomputable def embed (x : ℝ^n) : ℂ^n := .toLp 2 fun i ↦ ↑(x i)

/-- Define our notion of solution to the resolvent equation at transverse wavenumber k. -/
structure IsTransverseResolventSolution (k : ℝ) (l : ℂ) (v w : ℝ → ℂ^n) : Prop where
  /-- v is twice continuously differentiable. -/
  smooth : ContDiff ℝ 2 v
  /-- The first two derivatives of v are uniformly continuous. -/
  smooth_unif : ∀ i ≤ 2, UniformContinuous (iteratedDeriv i v ·)
  /-- v satisfies the resolvent equation. -/
  sol x : (D.complexify) ((Δ v x) - (k ^ 2) • (v x)) + c • (deriv v x) + (fderiv ℝ f (φ x)).complexify (v x) = w x

def TransverseSpectrum (k : ℝ) : Set ℂ :=
  compl {l | ∀ w, UniformContinuous w → ∃! v, IsTransverseResolventSolution f D c φ k l v w}

structure IsSpectrallyStableWithAdjoint : Prop where
  /-- Integrability of the adjoint eigenfunction. -/
  integrable : Integrable ψ
  /-- Normalization of the adjoint eigenfunction. -/
  normalized : ∫ x, ⟪ψ x, deriv φ x⟫_ℝ = 1
  /-- L₀ has a spectral gap. -/
  horizontal_spectral_gap : ∃ θ > 0, ∀ l ∈ TransverseSpectrum f D c φ 0, l = 0 ∨ l.re ≤ -θ
  /-- L₀ v = 0 implies v is a multiple of φ'. -/
  horizontal_kernel : ∀ v, IsTransverseResolventSolution f D c φ 0 0 v 0 →
    ∃ c : ℂ, ∀ x, v x = c • embed (deriv φ x)
  /-- L₀ v = w has a solution iff w is orthogonal to ψ. -/
  horizontal_solvability : ∀ w, UniformContinuous w →
     ∫ x, ⟪embed (ψ x), w x⟫_ℂ = 0 ↔ ∃ v, IsTransverseResolventSolution f D c φ 0 0 v w
  /-- Transverse spectral stability for small wavenumbers. -/
  transverse_low_wavenumber : d_perp D φ ψ > 0
  /-- Transverse spectral stability for medium-high wavenumbers. -/
  transverse_high_wavenumber : ∀ k₀ > 0, ∃ θ₁ > 0,
    ∀ k ≥ k₀, ∀ l ∈ TransverseSpectrum f D c φ k, l.re ≤ -θ₁

end SpectralStability

section NonlinearStability

/-- Extract the horizontal coordinate from x. -/
noncomputable def horizontal (x : ℝ^d) : ℝ := if hd : 1 ≤ d then x ⟨d - 1, by grind⟩ else 0

/-- Extract the transverse coordinates from x. -/
def transverse (x : ℝ^d) : ℝ^(d - 1) := .toLp 2 (fun i ↦ x ⟨i, by grind⟩)

/-- Assemble the full coordinate x from y and z. -/
def full (y : ℝ^(d - 1)) (z : ℝ) : ℝ^d :=
  .toLp 2 (fun i ↦ if h : i < d - 1 then y ⟨i, by grind⟩ else z)

/-- Define closeness to the front. -/
def IsCloseToFront (u : ℝ^d → ℝ^n) (ε : ℝ) : Prop := ∀ x, ‖u x - φ (horizontal x)‖ ≤ ε

/-- A solution to the RDE which starts close to a planar front is well-approximated by the front
shifted according to a viscous Hamilton-Jacobi equation.
-/
theorem vHJ_approximates_planar_front {t : ℝ}
  (hn : 1 ≤ n) (hd : 2 ≤ d) (ht : 0 < t)
  (h₁ : IsSmoothParabolic f D)
  (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
  ∃ C : ℝ, ∃ ε > 0, ∀ E_0 ∈ Icc 0 ε, ∀ u : ℝ → ℝ^d → ℝ^n,
      IsSmoothLocalRDESolution f D u t → IsCloseToFront φ (u 0) E_0 → ∃ σ,
        IsVHJSolution c σ (d_perp D φ ψ) ∧
        ∀ y, σ 0 y = ∫ z, ⟪ψ z, φ z - u 0 (full y z)⟫_ℝ ∧
        ∀ s ∈ Icc 0 t, ∀ x,
          ‖u s x - φ (x ⟨0, by grind⟩ - σ t (transverse x))‖ ≤ C * (E_0 ^ 2 + (1 + s)⁻¹ * E_0) := sorry

end NonlinearStability
