/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontRemainderConvolution
import Planarwave.Analysis.GaussianHeatKernel

/-!
# Decomposition of the full Fourier convolution

The second Fourier representation in Section 3 is proved here for the actual
transverse heat evolution on the translation mode. Integrating the symbol
decomposition then identifies the full Fourier convolution with this heat term
plus the previously constructed remainder convolution.

This does not yet identify the full Fourier convolution with the independently
constructed spatial semigroup; that is a separate remaining obligation.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.toNormedSpace

local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  (SeminormedAddGroup.toESeminormedAddMonoid
    (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))).toContinuousENorm

local instance : NormSMulClass ℝ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) := by
  exact NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))

/-- The transverse heat evolution of the zero-frequency translation projection. -/
def frontCriticalHeatEvolution (t : NNReal) (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) :
    BUC (ℝ^m) (BUC ℝ (ℂ^n)) :=
  heatFlowBUC (d_perp D φ ψ) t
    (BUC.postcompCLM (profileProjection ψ h₃.integrable
      (translationModeBUC f D c φ ψ h₃)) v)

omit [Nontrivial (ℝ^n)] in
/-- The second Fourier formula in Section 3, as an equality of longitudinal BUC values. -/
theorem frontCriticalHeatEvolution_eq_fourierIntegral (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (y : ℝ^m) :
    frontCriticalHeatEvolution f D c φ ψ h₃ t v y = ((2 * Real.pi) ^ m)⁻¹ •
      ∫ y' : ℝ^m, ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, y - y'⟫ : ℂ)) •
        (Complex.exp (-((d_perp D φ ψ * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) •
          (profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) (v y'))) := by
  simpa only [frontCriticalHeatEvolution, finrank_euclideanSpace_fin,
    BUC.postcompCLM_apply] using!
      (heatFlowBUC_eq_fourierIntegral h₃.transverse_low_wavenumber ht
        (BUC.postcompCLM (profileProjection ψ h₃.integrable
          (translationModeBUC f D c φ ψ h₃)) v) y)

/-- The normalized full Fourier kernel, defined from the full longitudinal symbol. -/
def frontFourierKernel (t : NNReal) (x : ℝ^m) : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  ((2 * Real.pi) ^ m)⁻¹ • oscillatoryIntegral
    (fun ξ : ℝ^m ↦ frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ)) x

/-- The full Fourier kernel splits into the Gaussian projection kernel and the
normalized remainder. Both frequency integrals are absolutely convergent. -/
theorem frontFourierKernel_decomposition (t : NNReal) (ht : 0 < t) (x : ℝ^m) :
    frontFourierKernel f D c φ h₁ h₂ t x =
      gaussianDensity (4 * d_perp D φ ψ * t)⁻¹ x •
        profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) +
      ((2 * Real.pi) ^ m)⁻¹ • frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x := by
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  have hsym (ξ : ℝ^m) : frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) =
      Complex.exp (-(t * d_perp D φ ψ : ℂ) * ‖ξ‖ ^ 2) • P +
        frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (embed ξ) := by
    rw [frontFourierRemainderSymbol, complexFrequencyQuadratic_embed]
    dsimp [P]
    abel
  have hR := integrable_frontFourierRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht 0 x
  have hzero : (embed (0 : ℝ^m) : ℂ^m) = 0 := by ext i; simp [embed]
  simp only [complexFrequencyShift, hzero, smul_zero, add_zero] at hR
  have hG : Integrable (fun ξ : ℝ^m ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      (Complex.exp (-(t * d_perp D φ ψ : ℂ) * ‖ξ‖ ^ 2) • P)) := by
    simpa only [Complex.ofReal_mul] using!
      integrable_oscillatory_gaussian_smul (mul_pos ht h₃.transverse_low_wavenumber) x P
  have hnorm : ((2 * Real.pi) ^ m)⁻¹ •
      oscillatoryIntegral (fun ξ : ℝ^m ↦
        Complex.exp (-(t * d_perp D φ ψ : ℂ) * ‖ξ‖ ^ 2) • P) x =
        gaussianDensity (4 * ((t : ℝ) * d_perp D φ ψ))⁻¹ x • P := by
    simpa only [Complex.ofReal_mul, finrank_euclideanSpace_fin] using!
      normalized_oscillatoryIntegral_gaussian_smul
        (mul_pos ht h₃.transverse_low_wavenumber) x P
  have hsmul (a : ℂ) (A B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :
      a • (A + B) = a • A + a • B := smul_add a A B
  have hsmulR (a : ℝ) (A B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :
      a • (A + B) = a • A + a • B := smul_add a A B
  rw [frontFourierKernel]
  simp only [oscillatoryIntegral, hsym, hsmul]
  rw [integral_add hG hR, hsmulR]
  rw [frontRemainderKernel_eq_integral]
  congr 1
  rw [show 4 * ((t : ℝ) * d_perp D φ ψ) = 4 * d_perp D φ ψ * t by ring] at hnorm
  simpa only [oscillatoryIntegral, finrank_euclideanSpace_fin] using! hnorm

include h₃ in
/-- Spatial continuity of the full operator-valued Fourier kernel. -/
theorem continuous_frontFourierKernel (t : NNReal) (ht : 0 < t) :
    Continuous (frontFourierKernel (m := m) f D c φ h₁ h₂ t) := by
  have he := funext (frontFourierKernel_decomposition (m := m) f D c φ h₁ h₂ ψ h₃ t ht)
  rw [he]
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  have hG : Continuous (fun x : ℝ^m ↦ gaussianDensity (4 * d_perp D φ ψ * t)⁻¹ x • P) := by
    simpa only using! (continuous_gaussianDensity (V := ℝ^m)
      (4 * d_perp D φ ψ * t)⁻¹).smul (continuous_const (y := P))
  simpa only using! hG.add
    ((continuous_frontRemainderKernel (m := m) f D c φ h₁ h₂ ψ h₃ t ht).const_smul
      (((2 * Real.pi) ^ m)⁻¹ : ℝ))

include h₃ in
/-- Absolute spatial integrability follows from the Gaussian and remainder bounds. -/
theorem integrable_frontFourierKernel (t : NNReal) (ht : 0 < t) :
    Integrable (frontFourierKernel (m := m) f D c φ h₁ h₂ t) := by
  have he := funext (frontFourierKernel_decomposition (m := m) f D c φ h₁ h₂ ψ h₃ t ht)
  rw [he]
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  have hb : 0 < (4 * d_perp D φ ψ * t)⁻¹ := by
    have := h₃.transverse_low_wavenumber
    positivity
  have hG : Integrable (fun x : ℝ^m ↦ gaussianDensity (4 * d_perp D φ ψ * t)⁻¹ x • P) := by
    simpa only using! (integrable_gaussianDensity (V := ℝ^m) hb).smul_const P
  have hR : Integrable (fun x : ℝ^m ↦ ((2 * Real.pi) ^ m)⁻¹ •
      frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x) := by
    simpa only using! (integrable_frontRemainderKernel (m := m) f D c φ h₁ h₂ ψ h₃ t ht).smul
      (((2 * Real.pi) ^ m)⁻¹ : ℝ)
  exact hG.add hR

/-- The full Fourier convolution, without yet asserting its semigroup identification. -/
def frontFourierConvolutionCLM (t : NNReal) (ht : 0 < t) :
    BUC (ℝ^m) (BUC ℝ (ℂ^n)) →L[ℂ] BUC (ℝ^m) (BUC ℝ (ℂ^n)) :=
  operatorConvolutionCLM
    (continuous_frontFourierKernel (m := m) f D c φ h₁ h₂ ψ h₃ t ht)
    (integrable_frontFourierKernel (m := m) f D c φ h₁ h₂ ψ h₃ t ht)

/-- Integrating the kernel decomposition gives exactly the heat evolution plus
the constructed remainder, in the BUC norm. -/
theorem frontFourierConvolutionCLM_decomposition (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) :
    frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v =
      frontCriticalHeatEvolution f D c φ ψ h₃ t v +
        frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v := by
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  let G : ℝ^m → BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    fun x ↦ gaussianDensity (4 * d_perp D φ ψ * t)⁻¹ x • P
  let R : ℝ^m → BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    fun x ↦ ((2 * Real.pi) ^ m)⁻¹ • frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x
  have hcG : Continuous G := (continuous_gaussianDensity _).smul continuous_const
  have hiG : Integrable G := (integrable_gaussianDensity
    (show 0 < (4 * d_perp D φ ψ * t)⁻¹ by
      have := h₃.transverse_low_wavenumber
      positivity)).smul_const P
  have hcR : Continuous R := by
    simpa only [R] using!
      (continuous_frontRemainderKernel (m := m) f D c φ h₁ h₂ ψ h₃ t ht).const_smul
        (((2 * Real.pi) ^ m)⁻¹ : ℝ)
  have hiR : Integrable R := by
    simpa only [R] using!
      (integrable_frontRemainderKernel (m := m) f D c φ h₁ h₂ ψ h₃ t ht).smul
        (((2 * Real.pi) ^ m)⁻¹ : ℝ)
  have he : frontFourierKernel f D c φ h₁ h₂ t = fun x ↦ G x + R x :=
    funext (frontFourierKernel_decomposition f D c φ h₁ h₂ ψ h₃ t ht)
  change operatorConvolution (μ := volume) _ v = _
  rw [he, operatorConvolution_add hcG hiG hcR hiR]
  have hheat : operatorConvolution (μ := volume) G v =
      frontCriticalHeatEvolution f D c φ ψ h₃ t v := by
    simpa only [G, P, frontCriticalHeatEvolution] using!
      operatorConvolution_gaussianDensity h₃.transverse_low_wavenumber ht P v
  rw [hheat]
  congr 1
  exact operatorConvolution_real_smul _ _ v

include h₃ in
/-- Absolute convergence of the full longitudinal-semigroup Fourier integral. -/
theorem integrable_frontFourierSemigroupIntegral (t : NNReal) (ht : 0 < t) (x : ℝ^m) :
    Integrable (fun ξ : ℝ^m ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ)) := by
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  have hR := integrable_frontFourierRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht 0 x
  have hzero : (embed (0 : ℝ^m) : ℂ^m) = 0 := by ext i; simp [embed]
  simp only [complexFrequencyShift, hzero, smul_zero, add_zero] at hR
  have hG : Integrable (fun ξ : ℝ^m ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      (Complex.exp (-(t * d_perp D φ ψ : ℂ) * ‖ξ‖ ^ 2) • P)) := by
    simpa only [Complex.ofReal_mul] using!
      integrable_oscillatory_gaussian_smul (mul_pos ht h₃.transverse_low_wavenumber) x P
  apply (hG.add hR).congr
  filter_upwards [] with ξ
  change Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      (Complex.exp (-(t * d_perp D φ ψ : ℂ) * ‖ξ‖ ^ 2) • P) +
      Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
        frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (embed ξ) = _
  rw [frontFourierRemainderSymbol, complexFrequencyQuadratic_embed]
  have hd (a : ℂ) (A B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :
      a • (A - B) = a • A - a • B := smul_sub a A B
  rw [hd]
  dsimp [P]
  abel

include h₃ in
/-- Applying the full Fourier kernel to a longitudinal slice commutes with its
absolutely convergent operator-valued frequency integral. -/
theorem frontFourierKernel_apply (t : NNReal) (ht : 0 < t) (x : ℝ^m)
    (v : BUC ℝ (ℂ^n)) :
    frontFourierKernel f D c φ h₁ h₂ t x v = ((2 * Real.pi) ^ m)⁻¹ •
      ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
        (frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) v) := by
  rw [frontFourierKernel, smul_apply]
  congr 1
  simpa only [oscillatoryIntegral, smul_apply] using!
    ContinuousLinearMap.integral_apply
      (integrable_frontFourierSemigroupIntegral f D c φ h₁ h₂ ψ h₃ t ht x) v

/-- The actual iterated Fourier formula for the full convolution, in the paper's
source-coordinate convention. This is not yet an identity for the spatial semigroup. -/
theorem frontFourierConvolutionCLM_apply_eq_fourierIntegral (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (y : ℝ^m) :
    frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v y =
      ((2 * Real.pi) ^ m)⁻¹ • ∫ y' : ℝ^m, ∫ ξ : ℝ^m,
        Complex.exp (Complex.I * (⟪ξ, y - y'⟫ : ℂ)) •
          (frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) (v y')) := by
  rw [frontFourierConvolutionCLM, operatorConvolutionCLM_apply,
    operatorConvolution_apply
      (continuous_frontFourierKernel f D c φ h₁ h₂ ψ h₃ t ht)
      (integrable_frontFourierKernel f D c φ h₁ h₂ ψ h₃ t ht)]
  have hsource : (∫ x : ℝ^m, frontFourierKernel f D c φ h₁ h₂ t x (v (y - x))) =
      ∫ y' : ℝ^m, frontFourierKernel f D c φ h₁ h₂ t (y - y') (v y') := by
    simpa only [sub_sub_cancel] using!
      (integral_sub_left_eq_self
        (fun x : ℝ^m ↦ frontFourierKernel f D c φ h₁ h₂ t x (v (y - x))) volume y).symm
  rw [hsource]
  simp_rw [frontFourierKernel_apply f D c φ h₁ h₂ ψ h₃ t ht]
  rw [integral_smul]

/-- The previously proved `C/t` estimate now bounds the difference between the
full Fourier convolution and the genuine translation-mode heat evolution. -/
theorem exists_frontFourierConvolution_heat_difference_bound :
    ∃ C > 0, ∀ (t : NNReal) (ht : 0 < t), 1 ≤ t →
      ∀ v : BUC (ℝ^m) (BUC ℝ (ℂ^n)),
        ‖frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v -
          frontCriticalHeatEvolution f D c φ ψ h₃ t v‖ ≤ (C / t) * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := exists_frontRemainderConvolutionCLM_decay_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨C, hC, fun t ht htone v ↦ ?_⟩
  rw [frontFourierConvolutionCLM_decomposition, add_sub_cancel_left]
  exact ((frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hb t ht htone) (norm_nonneg v))

end

end Planarwave
