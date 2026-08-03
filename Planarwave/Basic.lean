import Mathlib

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

open EuclideanGeometry ContDiff Laplacian Filter

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ : ℝ → ℝ^n)

structure HasPDESetup : Prop where
  smooth : ContDiff ℝ ∞ f
  positive : D.IsPositive
  kernel : Function.Injective D

noncomputable def ContinuousLinearMap.complexify {n : ℕ} (L : ℝ^n →L[ℝ] ℝ^n) :=
  Matrix.toEuclideanLin.symm L.toLinearMap|>.map (fun x ↦ (x : ℂ))|>.toEuclideanLin

structure IsSmoothFront : Prop where
  smooth : ContDiff ℝ 2 φ
  ode x : D (Δ φ x) + c • deriv φ x + f (φ x) = 0
  left_endpoint : ∃ φ₁, Tendsto φ atBot φ₁
  right_endpoint : ∃ φ₂, Tendsto φ atTop φ₂

structure IsTransverseResolventSolution (l : ℂ) (k : ℝ)  (v w : ℝ → ℂ^n) : Prop where
  smooth : ContDiff ℝ 2 v
  unif k (hk : k ≤ 2) : UniformContinuous (iteratedDeriv k v ·)
  sol x : (D.complexify) (Δ v x) - (k ^ 2) • D.complexify (v x) + (fderiv ℝ f (φ x)).complexify (v x) = w x

def TransverseSpectrum (k : ℝ) : Set ℂ :=
  {l | ∀ w, UniformContinuous w → ∃! v, IsTransverseResolventSolution f D φ l k v w}ᶜ

structure IsSpectrallyStableWith (κ : ℝ) (θ : ℝ) where
  hθ : θ > 0
  horizontal_spectral_gap : ∀ l ∈ TransverseSpectrum f D φ 0, l.re = 0 ∨ l.re ≤ -θ
  horizontal_simple_kernel : True
  transverse_low_wavenumber k (h : |k| ≤ κ) : ∀ l ∈ TransverseSpectrum f D φ k, l.re ≤ -θ * (k ^ 2)
  transverse_high_wavenumber k (h : κ ≤ |k|) : ∀ l ∈ TransverseSpectrum f D φ k, l.re ≤ -θ
