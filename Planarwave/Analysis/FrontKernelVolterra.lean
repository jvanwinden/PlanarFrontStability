/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDiffusionKernel
import all Planarwave.Analysis.FrontFourierDuhamel

/-!
# The spatial convolution equation for the full Fourier kernel

The inverse transform of the longitudinal Duhamel product is a spatial
convolution of the principal kernel, the reaction coefficient, and the full
kernel, in that order. This yields the kernel's Volterra identity. Passing the
identity to general bounded spatial data still requires spatial-time Fubini and
initial-value continuity; neither is inferred just from the kernel identity.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ}

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n)) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedAddCommGroup (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  (SeminormedAddGroup.toESeminormedAddMonoid
    (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))).toContinuousENorm
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.toNormedSpace

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- Strong continuity of the real-contour amplitude for a fixed longitudinal datum. -/
theorem continuous_frontFourierSymbol_apply (t : NNReal) (v : BUC ℝ (ℂ^n)) :
    Continuous (fun ξ : ℝ^m ↦ frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) v) := by
  let L : (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) →L[ℂ] BUC ℝ (ℂ^n) :=
    ContinuousLinearMap.apply ℂ (BUC ℝ (ℂ^n)) v
  have he : Continuous (fun ξ : ℝ^m ↦ (embed ξ : ℂ^m)) := by unfold embed; fun_prop
  exact L.continuous.comp ((contDiff_frontFourierSemigroupSymbol f D c φ h₁ h₂ t).continuous.comp he)

variable (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₃ in
/-- The positive-time symbol applied to any longitudinal datum is frequency integrable. -/
theorem integrable_frontFourierSymbol_apply (t : NNReal) (ht : 0 < t) (v : BUC ℝ (ℂ^n)) :
    Integrable (fun ξ : ℝ^m ↦ frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) v) := by
  have hi : Integrable (fun ξ : ℝ^m ↦ frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ)) := by
    simpa only [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] using!
      integrable_frontFourierSemigroupIntegral f D c φ h₁ h₂ ψ h₃ t ht (0 : ℝ^m)
  exact (ContinuousLinearMap.apply ℂ (BUC ℝ (ℂ^n)) v).integrable_comp hi

include h₃ in
/-- The inverse transform of `S₀(s,ξ) B S(r,ξ)` is its ordered kernel convolution.
Both times are positive; the Duhamel endpoints are treated separately as null sets. -/
theorem frontFourier_product_eq_kernel_convolution (s r : NNReal) (hs : 0 < s) (hr : 0 < r)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    ((2 * Real.pi) ^ m)⁻¹ • oscillatoryIntegral (fun ξ : ℝ^m ↦
      frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) s
        (frontReactionMultiplication f D c φ h₁ h₂
          (frontFourierSemigroupSymbol f D c φ h₁ h₂ r (embed ξ) v))) x =
      ∫ y : ℝ^m, frontDiffusionKernel D h₁.positive c s y
        (frontReactionMultiplication f D c φ h₁ h₂
          (frontFourierKernel f D c φ h₁ h₂ r (x - y) v)) := by
  let B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) := frontReactionMultiplication f D c φ h₁ h₂
  let g : ℝ^m → BUC ℝ (ℂ^n) := fun ξ ↦ frontFourierSemigroupSymbol f D c φ h₁ h₂ r (embed ξ) v
  let N : ℝ := ((2 * Real.pi) ^ m)⁻¹
  have hc : Continuous g := continuous_frontFourierSymbol_apply f D c φ h₁ h₂ r v
  have hi : Integrable g := integrable_frontFourierSymbol_apply f D c φ h₁ h₂ ψ h₃ r hr v
  have hB (a : ℝ) (w : BUC ℝ (ℂ^n)) : B (a • w) = a • B w :=
    (B.restrictScalars ℝ).map_smul a w
  have he (w : ℝ^m) : N • oscillatoryIntegral (fun ξ ↦ B (g ξ)) w =
      B (frontFourierKernel f D c φ h₁ h₂ r w v) := by
    rw [frontFourierKernel_apply f D c φ h₁ h₂ ψ h₃ r hr w v]
    change N • oscillatoryIntegral (fun ξ ↦ B (g ξ)) w = B (N • oscillatoryIntegral g w)
    rw [hB, map_oscillatoryIntegral B hc hi]
  have hconv : oscillatoryIntegral (fun ξ : ℝ^m ↦
      frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) s (B (g ξ))) x =
      ∫ y : ℝ^m, frontDiffusionKernel D h₁.positive c s y
        (oscillatoryIntegral (fun ξ ↦ B (g ξ)) (x - y)) := by
    simpa only [Function.comp_def] using!
      frontDiffusionKernel_fourier_convolution D h₁.positive c h₁.kernel s hs
        (B.continuous.comp hc) (B.integrable_comp hi) x
  change N • oscillatoryIntegral (fun ξ : ℝ^m ↦
      frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) s (B (g ξ))) x = _
  rw [hconv, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  have hK (a : ℝ) (w : BUC ℝ (ℂ^n)) :
      a • frontDiffusionKernel D h₁.positive c s y w =
        frontDiffusionKernel D h₁.positive c s y (a • w) :=
    ((frontDiffusionKernel D h₁.positive c s y).restrictScalars ℝ).map_smul a w |>.symm
  rw [hK, he]

include h₃ in
/-- Identify the actual inverse-transformed Duhamel integrand with spatial convolution. -/
theorem frontFourierDuhamel_inverse_eq_kernel_convolution (t : NNReal) {r : ℝ}
    (hr : r ∈ Ioo 0 (t : ℝ)) (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    ((2 * Real.pi) ^ m)⁻¹ •
      (∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
        frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v) =
      ∫ y : ℝ^m, frontDiffusionKernel D h₁.positive c ((t : ℝ) - r).toNNReal y
        (frontReactionMultiplication f D c φ h₁ h₂
          (frontFourierKernel f D c φ h₁ h₂ r.toNNReal (x - y) v)) := by
  have hs : 0 < ((t : ℝ) - r).toNNReal := Real.toNNReal_pos.mpr (sub_pos.mpr hr.2)
  have hrr : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr.1
  simpa only [oscillatoryIntegral, frontFourierDuhamelIntegrand,
    frontFourierSemigroupSymbol_embed, C0Semigroup.realOrbit] using!
    frontFourier_product_eq_kernel_convolution f D c φ h₁ h₂ ψ h₃
      ((t : ℝ) - r).toNNReal r.toNNReal hs hrr x v

include h₃ in
/-- Spatial Volterra identity for the full Fourier kernel, with the actual
principal diffusion kernel and actual front reaction multiplication. -/
theorem frontFourierKernel_volterra (t : NNReal) (ht : 0 < t)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    frontFourierKernel f D c φ h₁ h₂ t x v = frontDiffusionKernel D h₁.positive c t x v +
      ∫ r in 0..(t : ℝ), ∫ y : ℝ^m,
        frontDiffusionKernel D h₁.positive c ((t : ℝ) - r).toNNReal y
          (frontReactionMultiplication f D c φ h₁ h₂
            (frontFourierKernel f D c φ h₁ h₂ r.toNNReal (x - y) v)) := by
  rw [frontFourierKernel_duhamel f D c φ h₁ h₂ ψ h₃ t ht x v]
  have hfree := frontDiffusionKernel_eq_fourierIntegral D h₁.positive c h₁.kernel t ht x v
  simp only [oscillatoryIntegral] at hfree
  rw [← hfree]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (show 0 ≤ (t : ℝ) from t.2)
  intro r hr
  exact frontFourierDuhamel_inverse_eq_kernel_convolution f D c φ h₁ h₂ ψ h₃ t hr x v

include h₃ in
/-- The spatial convolution in the kernel Volterra equation is integrable in
time after spatial integration. This is not yet joint space-time integrability. -/
theorem intervalIntegrable_frontFourierKernel_convolution (t : NNReal) (ht : 0 < t)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    IntervalIntegrable (fun r : ℝ ↦ ∫ y : ℝ^m,
      frontDiffusionKernel D h₁.positive c ((t : ℝ) - r).toNNReal y
        (frontReactionMultiplication f D c φ h₁ h₂
          (frontFourierKernel f D c φ h₁ h₂ r.toNNReal (x - y) v))) volume 0 t := by
  have hi := (intervalIntegrable_frontFourierDuhamel_inverse f D c φ h₁ h₂ t ht x v).smul
    (((2 * Real.pi) ^ m)⁻¹ : ℝ)
  apply hi.congr_uIoo
  intro r hr
  have hr' : r ∈ Ioo 0 (t : ℝ) := uIoo_of_le (show 0 ≤ (t : ℝ) from t.2) ▸ hr
  exact frontFourierDuhamel_inverse_eq_kernel_convolution f D c φ h₁ h₂ ψ h₃ t hr' x v

end

end Planarwave
