/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianHeatKernel
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section

/-!
# Fourier inversion through a finite diffusion eigenbasis

The inner Gaussian Fourier integrals and their spatial integrals are integrable
separately. This justifies passing a fixed change of coordinates through the
iterated integral, without asserting joint integrability in frequency and space.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {V G H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- After frequency integration, the Gaussian Fourier amplitude is spatially
integrable even though the BUC amplitude itself need not be integrable. -/
theorem integrable_gaussianFourier_amplitude {b : ℝ} (hb : 0 < b) (v : BUC V G) (x : V) :
    Integrable (fun y : V ↦ oscillatoryIntegral
      (fun ξ : V ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) • v y) (x - y)) := by
  simp_rw [oscillatoryIntegral_gaussian_smul hb, Complex.coe_smul]
  have he (y : V) : -‖x - y‖ ^ 2 / (4 * b) = -(4 * b)⁻¹ * ‖x - y‖ ^ 2 := by ring
  simp_rw [he]
  let C := (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ)
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  have hi := ((integrable_gaussian_norm (V := V)
    (show 0 < (4 * b)⁻¹ by positivity)).comp_sub_left x).const_mul C
  apply (hi.mul_const ‖v‖).mono'
    (((by fun_prop : Continuous (fun y : V ↦
      (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(4 * b)⁻¹ * ‖x - y‖ ^ 2))).smul v.continuous).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖(C * Real.exp (-(4 * b)⁻¹ * ‖x - y‖ ^ 2)) • v y‖ ≤
    (C * Real.exp (-(4 * b)⁻¹ * ‖x - y‖ ^ 2)) * ‖v‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_left (v.norm_apply_le y) (mul_nonneg hC (Real.exp_pos _).le)

/-- A finite family of heat flows, followed by a fixed complex-linear coordinate
map, has the iterated Fourier representation obtained by diagonalizing diffusion. -/
theorem diagonal_heatFlowBUC_eq_fourierIntegral {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 < t)
    (v : ι → BUC V G) (J : (ι → G) →L[ℂ] H) (x : V) :
    J (fun i ↦ heatFlowBUC (a i) t (v i) x) =
      ((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ • ∫ y : V, ∫ ξ : V,
        Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) •
          J (fun i ↦ Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • v i y) := by
  let A (y ξ : V) : ι → G := fun i ↦
    Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) •
      (Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • v i y)
  have hi (y : V) : Integrable (A y) := Integrable.of_eval fun i ↦
    integrable_oscillatory_gaussian_smul (mul_pos (ha i) ht) (x - y) (v i y)
  have hval (y : V) (i : ι) : (∫ ξ : V, A y ξ) i =
      oscillatoryIntegral (fun ξ : V ↦ Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • v i y)
        (x - y) := eval_integral (fun i ↦ (hi y).eval i) i
  have ho : Integrable (fun y : V ↦ ∫ ξ : V, A y ξ) := by
    apply Integrable.of_eval
    intro i
    simp only [hval]
    exact integrable_gaussianFourier_amplitude (mul_pos (ha i) ht) (v i) x
  have hJ (y : V) : (∫ ξ : V,
      Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) •
        J (fun i ↦ Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • v i y)) =
        J (∫ ξ : V, A y ξ) := by
    have he (ξ : V) : J (A y ξ) =
        Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) •
          J (fun i ↦ Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • v i y) :=
      J.map_smul _ _
    simp_rw [← he]
    exact J.integral_comp_comm (hi y)
  simp_rw [hJ]
  rw [J.integral_comp_comm ho]
  have hlin (r : ℝ) (u : ι → G) : r • J u = J (r • u) :=
    ((J.restrictScalars ℝ).map_smul r u).symm
  rw [hlin]
  congr 1
  funext i
  rw [Pi.smul_apply, eval_integral (fun i ↦ ho.eval i)]
  simp only [hval]
  exact heatFlowBUC_eq_fourierIntegral (ha i) ht (v i) x

end

end Planarwave
