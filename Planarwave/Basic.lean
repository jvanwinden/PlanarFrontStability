import Mathlib

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

open EuclideanGeometry ContDiff Laplacian Filter

variable (n : ℕ) (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ : ℝ → ℝ^n)

structure HasPDESetup : Prop where
  smooth : ContDiff ℝ ∞ f
  strict_positive : D.IsPositive ∧ Function.Injective D

structure IsSmoothFront : Prop where
  smooth : ContDiff ℝ 2 φ
  ode x : D (Δ φ x) + c • deriv φ x + f (φ x) = 0
  left_endpoint : ∃ φ₁, Tendsto φ atBot φ₁
  right_endpoint : ∃ φ₂, Tendsto φ atTop φ₂

structure IsTransverseResolventSolution (k : ℝ) (l : ℂ) (v w : ℝ → ℂ^n) : Prop where
  smooth : ContDiff ℝ 2 v
  unif k (hk : k ≤ 2) : UniformContinuous (iteratedDeriv k v ·)
  sol x : (Δ v x) = 0
  sol x : D (Δ v x) - k ^ 2 • D (v x) + c • deriv v x + (fderiv ℝ f (φ x)) (v x) = w x

structure IsInTransverseResolve (λ : ℂ)

def operator_spectrum : Set ℝ :=
    {}

structure IsSpectrallyStable : Prop where
  kernel : True
