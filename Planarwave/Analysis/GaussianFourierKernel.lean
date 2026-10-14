/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-!
# Absolutely convergent operator-valued Fourier kernels

The frequency estimates in Section 2 give Gaussian domination on each shifted
real contour. This file turns that domination into a genuine Banach-valued
integral, retaining the dimension-dependent Gaussian mass. The convention is
the paper's `exp(i ⟨ξ,x⟩)`; the Fourier normalization is inserted only when
constructing the spatial convolution operator.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The real Gaussian frequency majorant is integrable in every finite dimension. -/
theorem integrable_gaussian_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V ↦ Real.exp (-b * ‖ξ‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using! h

/-- Unnormalized inverse Fourier integral, as used in the paper's kernel `H`. -/
def oscillatoryIntegral (g : V → F) (x : V) : F :=
  ∫ ξ : V, Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) • g ξ

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] in
/-- The oscillatory factor has unit norm on the real contour. -/
theorem norm_oscillatoryIntegrand (g : V → F) (x ξ : V) :
    ‖Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) • g ξ‖ = ‖g ξ‖ := by
  simp [norm_smul, Complex.norm_exp]

omit [CompleteSpace F] in
/-- A continuous Gaussian-dominated symbol has an absolutely convergent Fourier integral. -/
theorem integrable_oscillatory_of_gaussian_bound {g : V → F} (hg : Continuous g)
    {b C : ℝ} (hb : 0 < b) (hbound : ∀ ξ, ‖g ξ‖ ≤ C * Real.exp (-b * ‖ξ‖ ^ 2)) (x : V) :
    Integrable (fun ξ : V ↦ Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) • g ξ) := by
  have hc : Continuous (fun ξ : V ↦ Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) • g ξ) := by
    fun_prop
  apply ((integrable_gaussian_norm (V := V) hb).const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ ↦ (norm_oscillatoryIntegrand g x ξ).trans_le (hbound ξ)

omit [CompleteSpace F] in
/-- Integrating the Gaussian domination gives the exact dimensional mass factor. -/
theorem norm_oscillatoryIntegral_le_gaussian {g : V → F} (hg : Continuous g)
    {b C : ℝ} (hb : 0 < b) (hbound : ∀ ξ, ‖g ξ‖ ≤ C * Real.exp (-b * ‖ξ‖ ^ 2)) (x : V) :
    ‖oscillatoryIntegral g x‖ ≤ C * (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ) := by
  have hint := integrable_oscillatory_of_gaussian_bound hg hb hbound x
  calc
    ‖oscillatoryIntegral g x‖ ≤
        ∫ ξ : V, ‖Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) • g ξ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : V, C * Real.exp (-b * ‖ξ‖ ^ 2) :=
      integral_mono hint.norm ((integrable_gaussian_norm hb).const_mul C)
        (fun ξ ↦ (norm_oscillatoryIntegrand g x ξ).trans_le (hbound ξ))
    _ = _ := by rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb]

omit [CompleteSpace F] in
/-- Gaussian domination also gives norm-continuity of the Fourier kernel in the
spatial displacement, by dominated convergence. -/
theorem continuous_oscillatoryIntegral_of_gaussian_bound {g : V → F} (hg : Continuous g)
    {b C : ℝ} (hb : 0 < b) (hbound : ∀ ξ, ‖g ξ‖ ≤ C * Real.exp (-b * ‖ξ‖ ^ 2)) :
    Continuous (oscillatoryIntegral g) := by
  apply continuous_of_dominated (bound := fun ξ : V ↦ C * Real.exp (-b * ‖ξ‖ ^ 2))
  · intro x
    exact (integrable_oscillatory_of_gaussian_bound hg hb hbound x).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun ξ ↦ (norm_oscillatoryIntegrand g x ξ).trans_le (hbound ξ)
  · exact (integrable_gaussian_norm hb).const_mul C
  · filter_upwards [] with ξ
    fun_prop

end

end Planarwave
