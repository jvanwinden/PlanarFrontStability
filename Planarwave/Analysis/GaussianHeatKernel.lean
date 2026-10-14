/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianFourierKernel
public import Planarwave.Analysis.HeatSemigroup
public import Planarwave.Analysis.BUCOperatorConvolution

@[expose] public section

/-!
# The heat kernel and the paper's Fourier normalization

This identifies the Gaussian Fourier integral with the independently defined
Gaussian heat flow. All integral representations here are for positive time;
no spatial integrability of the bounded initial datum is required.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Exact inverse Fourier transform of a scalar Gaussian, before normalization. -/
theorem oscillatoryIntegral_gaussian {b : ℝ} (hb : 0 < b) (x : V) :
    oscillatoryIntegral (fun ξ : V ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2)) x =
      (((Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-‖x‖ ^ 2 / (4 * b)) : ℝ) : ℂ) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) (by simpa using hb) Complex.I x
  calc
    _ = ∫ ξ : V, Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 +
        Complex.I * (⟪x, ξ⟫ : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [smul_eq_mul, ← Complex.exp_add, real_inner_comm ξ x]
      congr 1
      ring
    _ = _ := by
      rw [h]
      simp only [Complex.ofReal_mul, Complex.ofReal_exp,
        Complex.ofReal_cpow (show 0 ≤ Real.pi / b by positivity),
        Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat,
        Complex.ofReal_neg, Complex.ofReal_pow, Complex.I_sq]
      congr 2
      ring

/-- A real Gaussian density, normalized by its exact dimensional mass. -/
def gaussianDensity (b : ℝ) (x : V) : ℝ :=
  ((Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ))⁻¹ * Real.exp (-b * ‖x‖ ^ 2)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem continuous_gaussianDensity (b : ℝ) : Continuous (gaussianDensity (V := V) b) := by
  unfold gaussianDensity
  fun_prop

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem gaussianDensity_nonneg {b : ℝ} (hb : 0 < b) (x : V) :
    0 ≤ gaussianDensity b x := by
  unfold gaussianDensity
  positivity

theorem integrable_gaussianDensity {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianDensity (V := V) b) :=
  (integrable_gaussian_norm hb).const_mul _

theorem integral_gaussianDensity {b : ℝ} (hb : 0 < b) :
    ∫ x : V, gaussianDensity b x = 1 := by
  simp only [gaussianDensity]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))

/-- The normalized density defines a probability measure. -/
theorem isProbabilityMeasure_gaussianDensity {b : ℝ} (hb : 0 < b) :
    IsProbabilityMeasure
      (volume.withDensity (fun x : V ↦ ENNReal.ofReal (gaussianDensity b x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianDensity hb)
      (ae_of_all _ (gaussianDensity_nonneg hb)), integral_gaussianDensity hb]
  simp

/-- Characteristic function of the normalized Gaussian density. -/
theorem charFun_gaussianDensity {b : ℝ} (hb : 0 < b) (w : V) :
    charFun (volume.withDensity (fun x : V ↦ ENNReal.ofReal (gaussianDensity b x))) w =
      Complex.exp ((-‖w‖ ^ 2 / (4 * b) : ℝ) : ℂ) := by
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul
    ((continuous_gaussianDensity b).measurable.ennreal_ofReal)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hn : ∀ x : V, (ENNReal.ofReal (gaussianDensity b x)).toReal =
      gaussianDensity b x := fun x ↦ ENNReal.toReal_ofReal (gaussianDensity_nonneg hb x)
  simp only [hn]
  simp only [gaussianDensity, mul_smul, integral_smul]
  have hi : (∫ x : V, Real.exp (-b * ‖x‖ ^ 2) •
      Complex.exp ((⟪x, w⟫ : ℂ) * Complex.I)) =
      oscillatoryIntegral (fun x : V ↦ Complex.exp (-(b : ℂ) * ‖x‖ ^ 2)) w := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Complex.real_smul, Complex.ofReal_exp, mul_comm]
  rw [hi, oscillatoryIntegral_gaussian hb]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [← mul_assoc, inv_mul_cancel₀, one_mul, Complex.ofReal_exp]
  exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (show 0 < Real.pi / b by positivity)
    (Module.finrank ℝ V / 2 : ℝ)))

/-- The positive-time heat measure has the normalized Gaussian Lebesgue density. -/
theorem heatMeasure_eq_withDensity {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    heatMeasure (E := V) a t = volume.withDensity
      (fun x : V ↦ ENNReal.ofReal (gaussianDensity (4 * a * t)⁻¹ x)) := by
  have hb : 0 < (4 * a * t)⁻¹ := by positivity
  let _ := isProbabilityMeasure_gaussianDensity (V := V) hb
  apply Measure.ext_of_charFun
  funext w
  rw [charFun_heatMeasure ha.le ht.le, charFun_gaussianDensity hb]
  congr 1
  push_cast
  field_simp

/-- The factor `(2π)⁻ᵐ` converts the Fourier Gaussian mass to the heat-kernel mass. -/
theorem gaussian_fourier_normalization {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ((2 * Real.pi) ^ m)⁻¹ * (Real.pi / b) ^ (m / 2 : ℝ) =
      ((Real.pi / (4 * b)⁻¹) ^ (m / 2 : ℝ))⁻¹ := by
  have hprod : (Real.pi / b) ^ (m / 2 : ℝ) *
      (Real.pi / (4 * b)⁻¹) ^ (m / 2 : ℝ) = (2 * Real.pi) ^ m := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have heq : (Real.pi / b) * (Real.pi / (4 * b)⁻¹) = (2 * Real.pi) ^ 2 := by
      field_simp
      ring
    rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (m / 2 : ℝ) = m by ring, Real.rpow_natCast]
  rw [← hprod, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (show 0 < Real.pi / b by positivity) _)),
    mul_one]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- Absolute convergence also holds with any fixed Banach-valued amplitude. -/
theorem integrable_oscillatory_gaussian_smul {b : ℝ} (hb : 0 < b) (x : V) (v : G) :
    Integrable (fun ξ : V ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      (Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) • v)) := by
  apply integrable_oscillatory_of_gaussian_bound (by fun_prop) hb
    (C := ‖v‖) ?_ x
  intro ξ
  simp [norm_smul, Complex.norm_exp, ← Complex.ofReal_pow, mul_comm]

/-- Pulling a fixed vector or operator out of the Gaussian Fourier integral. -/
theorem oscillatoryIntegral_gaussian_smul {b : ℝ} (hb : 0 < b) (x : V) (v : G) :
    oscillatoryIntegral (fun ξ : V ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) • v) x =
      (((Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-‖x‖ ^ 2 / (4 * b)) : ℝ) : ℂ) • v := by
  simp only [oscillatoryIntegral, smul_smul, integral_smul_const]
  rw [← oscillatoryIntegral_gaussian hb x]
  rfl

/-- Normalized Gaussian Fourier inversion for a Banach-valued amplitude. -/
theorem normalized_oscillatoryIntegral_gaussian_smul {b : ℝ} (hb : 0 < b)
    (x : V) (v : G) :
    (((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ : ℝ) •
        oscillatoryIntegral (fun ξ : V ↦ Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) • v) x =
      gaussianDensity (4 * b)⁻¹ x • v := by
  rw [oscillatoryIntegral_gaussian_smul hb, Complex.coe_smul,
    smul_smul, ← mul_assoc, gaussian_fourier_normalization hb]
  congr 1
  unfold gaussianDensity
  congr 2
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Lebesgue convolution formula for the existing Gaussian heat flow. -/
theorem heatFlow_eq_integral_gaussianDensity {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : V → F) (hf : Continuous f) (x : V) :
    heatFlow a t f x = ∫ y : V, gaussianDensity (4 * a * t)⁻¹ y • f (x - y) := by
  rw [heatFlow_eq_integral_heatMeasure a t f hf x, heatMeasure_eq_withDensity ha ht,
    integral_withDensity_eq_integral_toReal_smul
      ((continuous_gaussianDensity _).measurable.ennreal_ofReal)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hn : ∀ y : V, (ENNReal.ofReal (gaussianDensity (4 * a * t)⁻¹ y)).toReal =
      gaussianDensity (4 * a * t)⁻¹ y := fun y ↦
    ENNReal.toReal_ofReal (gaussianDensity_nonneg (by positivity) y)
  simp only [hn]
  rw [← integral_neg_eq_self (fun y : V ↦ gaussianDensity (4 * a * t)⁻¹ y • f (x + y))]
  simp [gaussianDensity, sub_eq_add_neg]

/-- The Gaussian convolution is a genuine BUC-valued operator convolution. -/
theorem operatorConvolution_gaussianDensity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (P : E →L[ℂ] G) (v : BUC V E) :
    operatorConvolution (μ := volume) (fun x : V ↦ gaussianDensity (4 * a * t)⁻¹ x • P) v =
      heatFlowBUC a t (BUC.postcompCLM P v) := by
  apply BUC.ext
  intro x
  calc
    _ = ∫ y : V, gaussianDensity (4 * a * t)⁻¹ y • P (v (x - y)) := by
      simpa only [smul_apply] using!
        (operatorConvolution_apply (𝕜 := ℂ) (E := E) (F := G) (μ := volume)
          (K := fun y : V ↦ gaussianDensity (4 * a * t)⁻¹ y • P)
          ((continuous_gaussianDensity _).smul continuous_const)
          ((integrable_gaussianDensity (show 0 < (4 * a * t)⁻¹ by positivity)).smul_const P)
          v x)
    _ = _ := by
      simpa only [heatFlowBUC_apply, BUC.postcompCLM_apply] using!
        (heatFlow_eq_integral_gaussianDensity (F := G) ha ht
          (BUC.postcompCLM P v) (BUC.postcompCLM P v).continuous x).symm

/-- The paper's iterated inverse Fourier formula for the heat flow. The inner
integral is evaluated first; no false joint-integrability assumption is used. -/
theorem heatFlowBUC_eq_fourierIntegral {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (v : BUC V G) (x : V) :
    heatFlowBUC a t v x = ((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ •
      ∫ y : V, ∫ ξ : V, Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) •
        (Complex.exp (-((a * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • v y) := by
  rw [heatFlowBUC_apply, heatFlow_eq_integral_gaussianDensity ha ht v v.continuous x,
    ← integral_smul]
  have hpoint (y : V) : ((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ •
      (∫ ξ : V, Complex.exp (Complex.I * (⟪ξ, x - y⟫ : ℂ)) •
        (Complex.exp (-((a * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • v y)) =
        gaussianDensity (4 * a * t)⁻¹ (x - y) • v y := by
    simpa only [mul_assoc, oscillatoryIntegral] using
      normalized_oscillatoryIntegral_gaussian_smul (mul_pos ha ht) (x - y) (v y)
  simp_rw [hpoint]
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun y : V ↦ gaussianDensity (4 * a * t)⁻¹ y • v (x - y)) volume x).symm

end

end Planarwave
