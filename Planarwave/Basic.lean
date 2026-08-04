import Mathlib

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

open EuclideanGeometry ContDiff Laplacian Filter Gradient Set

-- PDE data: dimension, nonlinearity, diffusion matrix.
variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
-- Front data: speed, profile, transverse diffusion coefficient
variable (c : ℝ) (φ : ℝ → ℝ^n) (d_perp : ℝ)
-- Prospective solutions to the relevant PDEs.
variable (u : ℝ → ℝ^d → ℝ^n) (σ : ℝ → ℝ^(d - 1) → ℝ)

section PDESetup

/-- The PDE is uniformly parabolic and the nonlinearity is smooth. -/
structure IsSmoothParabolic : Prop where
  smooth : ContDiff ℝ ∞ f
  positive : D.IsPositive
  kernel : Function.Injective D

/-- Define our notion of (local) solution for the reaction-diffusion equation. -/
structure IsSmoothLocalRDESolution (t : ℝ) : Prop where
  cont : ∀ s ∈ Icc 0 t, UniformContinuousOn (Function.uncurry u) (Icc 0 s ×ˢ univ)
  smooth : ContDiffOn ℝ ∞ (Function.uncurry u) (Ioc 0 t ×ˢ univ)
  pde : ∀ s ∈ Ioc 0 t, ∀ x, deriv (u · x) s = D (Δ (u s ·) x) + f (u s x)

/-- Define our notion of (global) solution for the viscous Hamilton-Jaboci equation. -/
structure IsVHJSolution : Prop where
  cont : ∀ s ∈ Set.Ici 0, UniformContinuousOn (Function.uncurry σ) (Set.Icc 0 s ×ˢ Set.univ)
  smooth : ContDiffOn ℝ ∞ (Function.uncurry σ) (Set.Ioi 0 ×ˢ Set.univ)
  pde : ∀ t ∈ Ioi 0, ∀ y, deriv (σ · y) t = c + d_perp * (Δ (σ t ·) y) + ((c ^ 2) / 2) * ‖∇ (σ t ·) y‖^2

end PDESetup

/-- The front is twice continuously differentiable, has left and right limits, and satisfies the
traveling wave ODE. -/
structure IsSmoothFront : Prop where
  smooth : ContDiff ℝ 2 φ
  ode x : D (Δ φ x) + c • deriv φ x + f (φ x) = 0
  left_endpoint : ∃ φ₁, Tendsto φ atBot φ₁
  right_endpoint : ∃ φ₂, Tendsto φ atTop φ₂

section SpectralStability

noncomputable def ContinuousLinearMap.complexify (L : ℝ^n →L[ℝ] ℝ^n) :=
  Matrix.toEuclideanLin.symm L.toLinearMap|>.map (fun x ↦ (x : ℂ))|>.toEuclideanLin

noncomputable def embed (x : ℝ^n) : ℂ^n := WithLp.toLp 2 (fun i ↦ (x i : ℂ))

/-- Define our notion of solution to the resolvent equation at transverse wavenumber k. -/
structure IsTransverseResolventSolution (l : ℂ) (k : ℝ) (v w : ℝ → ℂ^n) : Prop where
  /-- v is twice continuously differentiable. -/
  smooth : ContDiff ℝ 2 v
  /-- The first two derivatives of v are uniformly continuous. -/
  unif k (hk : k ≤ 2) : UniformContinuous (iteratedDeriv k v ·)
  /-- v satisfies the resolvent equation. -/
  sol x : (D.complexify) (Δ v x) - (k ^ 2) • D.complexify (v x) +
    c • (deriv v x) + (fderiv ℝ f (φ x)).complexify (v x) = w x

def TransverseSpectrum (k : ℝ) : Set ℂ :=
  {l | ∀ w, UniformContinuous w → ∃! v, IsTransverseResolventSolution f D c φ l k v w}ᶜ

structure IsSpectrallyStableWith (ψ : ℝ → ℝ^n) (k₀ : ℝ) (θ : ℝ) : Prop where
  theta_pos : θ > 0
  /-- Integrability of the adjoint eigenfunction. -/
  integrable : MeasureTheory.Integrable ψ
  /-- Spectral gap for k = 0. -/
  horizontal_spectral_gap : ∀ l ∈ TransverseSpectrum f D c φ 0, l = 0 ∨ l.re ≤ -θ
  /-- Uniqueness modulo the translational eigenfunction. -/
  zero_almost_unique : ∀ w, UniformContinuous w → ∀ v₁ v₂,
    IsTransverseResolventSolution f D c φ 0 0 v₁ w → IsTransverseResolventSolution f D c φ 0 0 v₂ w →
    ∃ c : ℂ, ∀ x, v₁ x - v₂ x = c • (fun i ↦ (deriv φ x i : ℂ))
  /-- Solvability under an orthogonality condition. -/
  horizontal_almost_solvable : ∀ w, UniformContinuous w → ∫ x, inner ℂ (w x) (embed (ψ x)) = 0 →
    ∃ v, IsTransverseResolventSolution f D c φ 0 0 v w
  /-- Transverse spectral stability for small wavenumbers. -/
  transverse_low_wavenumber : ∀ k ∈ Set.Icc 0 k₀, ∀ l ∈ TransverseSpectrum f D c φ k, l.re ≤ -θ * (k ^ 2)
  /-- Transverse spectral stability for medium-high wavenumbers. -/
  transverse_high_wavenumber : ∀ k ∈ Set.Ici k₀, ∀ l ∈ TransverseSpectrum f D c φ k, l.re ≤ -θ

end SpectralStability

section NonlinearStability

/-- Extract the horizontal coordinate from x. -/
def horizontal (x : ℝ^d) : ℝ := sorry

/-- Extract the transverse coordinates from x. -/
def transverse (x : ℝ^d) : ℝ^(d - 1) := sorry

/-- Define closeness to the front. -/
def IsCloseToFront (u : ℝ^d → ℝ^n) (ε : ℝ) : Prop := ∀ x, ‖u x - φ (horizontal x)‖ ≤ ε

/-- A solution to the RDE which starts close to a planar front is well-approximated by the front
shifted according to a viscous Hamilton-Jacobi equation.
-/
theorem vHJ_approximates_planar_front
  (hn : 1 ≤ n) (hd : 2 ≤ d)
  (t : ℝ) (ht : 0 < t)
  (h₁ : IsSmoothParabolic f D)
  (h₂ : IsSmoothFront f D c φ)
  (h₃ : ∃ ψ k₀ θ, IsSpectrallyStableWith f D c φ ψ k₀ θ) :
  ∃ C : ℝ, ∃ d_perp > 0, ∃ ε > 0,
    ∀ E_0 ∈ Set.Icc 0 ε, ∀ u : ℝ → ℝ^d → ℝ^n,
      IsSmoothLocalRDESolution f D u t → IsCloseToFront φ (u 0) E_0 →
        ∃ σ : ℝ → ℝ^(d - 1) → ℝ, IsVHJSolution c d_perp σ ∧
          ∀ x, ∀ s ∈ Set.Icc 0 t,
            ‖u s x - φ (x ⟨0, by grind⟩ - σ t (transverse x))‖ ≤ C * (E_0 ^ 2 + (1 + s)⁻¹ * E_0) := sorry

end NonlinearStability
