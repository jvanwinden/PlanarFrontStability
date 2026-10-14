/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianHeatKernel
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Gaussian multipliers and spatial convolution

Multiplication by a Gaussian in frequency becomes convolution with the normalized
Gaussian density in space. Fubini is justified by the product of the integrable
Gaussian density and the integrable frequency amplitude. The amplitude may be
Banach-valued; no integrability of its inverse transform is needed for this step.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- A real Fourier phase preserves absolute integrability of the amplitude. -/
theorem integrable_oscillatory_of_integrable {g : V → G}
    (hg : Continuous g) (hi : Integrable g) (x : V) :
    Integrable (fun ξ ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) • g ξ) := by
  apply hi.norm.mono' (by fun_prop : Continuous
    (fun ξ ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) • g ξ)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ ↦ (norm_oscillatoryIntegrand g x ξ).le

omit [CompleteSpace G] in
/-- A nonnegative Gaussian multiplier cannot increase the frequency integrability norm. -/
theorem integrable_gaussian_mul_of_integrable {b : ℝ} (hb : 0 ≤ b)
    {g : V → G} (hg : Continuous g) (hi : Integrable g) :
    Integrable (fun ξ ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) • g ξ) := by
  apply hi.norm.mono' (by fun_prop : Continuous
    (fun ξ ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) • g ξ)).aestronglyMeasurable
  filter_upwards [] with ξ
  rw [norm_smul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _)

/-- The Fourier transform of the spatial Gaussian, in the paper's phase convention. -/
theorem integral_gaussianDensity_phase {b : ℝ} (hb : 0 < b) (ξ : V) :
    (∫ y : V, gaussianDensity (4 * b)⁻¹ y •
      Complex.exp (Complex.I * (⟪ξ, y⟫ : ℂ))) = Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) := by
  have hpos : 0 < (4 * b)⁻¹ := by positivity
  have hc := charFun_gaussianDensity (V := V) hpos ξ
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul
    ((continuous_gaussianDensity _).measurable.ennreal_ofReal)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at hc
  simp only [ENNReal.toReal_ofReal (gaussianDensity_nonneg hpos _)] at hc
  have he : ((-‖ξ‖ ^ 2 / (4 * (4 * b)⁻¹) : ℝ) : ℂ) = -(b : ℂ) * ‖ξ‖ ^ 2 := by
    push_cast
    field_simp
  rw [he] at hc
  simpa only [real_inner_comm, mul_comm] using hc

/-- Integrating the translated phase leaves the heat multiplier and the original phase. -/
theorem integral_gaussianDensity_translated_phase {b : ℝ} (hb : 0 < b) (x ξ : V) :
    (∫ y : V, gaussianDensity (4 * b)⁻¹ y •
      Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ))) =
        Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) * Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) := by
  have hp (y : V) : Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) =
      Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) * Complex.exp (Complex.I * (⟪-ξ, y⟫ : ℂ)) := by
    rw [← Complex.exp_add, inner_sub_right, inner_neg_left]
    push_cast
    congr 1
    ring
  have he (y : V) : gaussianDensity (4 * b)⁻¹ y •
      Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) =
      (gaussianDensity (4 * b)⁻¹ y • Complex.exp (Complex.I * (⟪-ξ, y⟫ : ℂ))) *
        Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) := by
    rw [hp, mul_comm (Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)))
      (Complex.exp (Complex.I * (⟪-ξ, y⟫ : ℂ))), smul_mul_assoc]
  simp_rw [he]
  rw [integral_mul_const, integral_gaussianDensity_phase hb]
  simp only [norm_neg, mul_comm]

omit [CompleteSpace G] in
/-- Joint absolute convergence of the Gaussian-space/frequency integral. -/
theorem integrable_gaussian_oscillatory_product {b : ℝ} (hb : 0 < b)
    {g : V → G} (hg : Continuous g) (hi : Integrable g) (x : V) :
    Integrable (fun p : V × V ↦ gaussianDensity (4 * b)⁻¹ p.1 •
      (Complex.exp (Complex.I * (⟪p.2, x - p.1⟫ : ℂ)) • g p.2)) := by
  have hpos : 0 < (4 * b)⁻¹ := by positivity
  have hdom := (integrable_gaussianDensity (V := V) hpos).mul_prod hi.norm
  have hρ := (continuous_gaussianDensity (V := V) (4 * b)⁻¹).comp
    (continuous_fst : Continuous (fun p : V × V ↦ p.1))
  rw [Measure.volume_eq_prod]
  apply hdom.mono' (by fun_prop : Continuous (fun p : V × V ↦
    gaussianDensity (4 * b)⁻¹ p.1 •
      (Complex.exp (Complex.I * (⟪p.2, x - p.1⟫ : ℂ)) • g p.2))).aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gaussianDensity_nonneg hpos _),
    norm_oscillatoryIntegrand]

/-- A Gaussian frequency multiplier is exactly Gaussian convolution in space. -/
theorem oscillatoryIntegral_gaussian_mul_eq_convolution {b : ℝ} (hb : 0 < b)
    {g : V → G} (hg : Continuous g) (hi : Integrable g) (x : V) :
    oscillatoryIntegral (fun ξ : V ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) • g ξ) x =
      ∫ y : V, gaussianDensity (4 * b)⁻¹ y • oscillatoryIntegral g (x - y) := by
  have hprod := integrable_gaussian_oscillatory_product hb hg hi x
  rw [Measure.volume_eq_prod] at hprod
  unfold oscillatoryIntegral
  simp_rw [← integral_smul]
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hs (r : ℝ) (z : ℂ) (v : G) : r • (z • v) = (r • z) • v := (smul_assoc r z v).symm
  simp_rw [hs]
  rw [integral_smul_const, integral_gaussianDensity_translated_phase hb]
  exact (mul_smul _ _ _).symm

omit [CompleteSpace G] in
/-- The convolution side is integrable as a Banach-valued spatial integral. -/
theorem integrable_gaussian_oscillatory_convolution {b : ℝ} (hb : 0 < b)
    {g : V → G} (hg : Continuous g) (hi : Integrable g) (x : V) :
    Integrable (fun y : V ↦ gaussianDensity (4 * b)⁻¹ y • oscillatoryIntegral g (x - y)) := by
  have hprod := integrable_gaussian_oscillatory_product hb hg hi x
  rw [Measure.volume_eq_prod] at hprod
  simpa only [integral_smul, oscillatoryIntegral] using! hprod.integral_prod_left

end

end Planarwave
