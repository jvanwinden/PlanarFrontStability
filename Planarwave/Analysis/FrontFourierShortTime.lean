/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierDecomposition

/-!
# Uniform short-time bounds for the Fourier convolution

For the Volterra identification, the Fourier convolution must also be controlled
near time zero. Apply the paper's contour shift at all positive times, retaining
the harmless exponential growth. The spatial Gaussian mass cancels the frequency
Gaussian mass, giving a uniform bound on each bounded time interval.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  (SeminormedAddGroup.toESeminormedAddMonoid
    (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))).toContinuousENorm
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  ContinuousLinearMap.toNormedSpace

/-- A Gaussian spatial majorant valid at every positive time, including near zero. -/
theorem exists_frontRemainderKernel_allTime_gaussian_bound :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∃ ν > 0, ∀ (t : NNReal), 0 < t → ∀ x : ℝ^m,
      ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ ≤
        M * (Real.pi / (μ * t)) ^ (m / 2 : ℝ) * Real.exp (κ * t) *
          Real.exp (-(ν / t) * ‖x‖ ^ 2) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, hb⟩ :=
    exists_frontShiftedRemainderKernel_gaussian_bound (m := m) f D c φ h₁ h₂ ψ h₃
  let ε : ℝ := (2 * κ)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : κ * ε ≤ 1 / 2 := by dsimp [ε]; field_simp; norm_num
  refine ⟨M, hM, μ, hμ, κ, hκ, ε / 2, half_pos hε, ?_⟩
  intro t ht x
  have hs := onDiagonal_shift_exponent_le (t := (t : ℝ)) hε.le ht hsmall x
  rw [← frontShiftedRemainderKernel_eq f D c φ h₁ h₂ ψ h₃ t ht ((ε / t) • x) x]
  apply (hb t ht ((ε / t) • x) x).trans
  calc
    _ ≤ M * (Real.pi / (μ * t)) ^ (m / 2 : ℝ) *
        Real.exp (κ * t + (-(ε / 2) * ‖x‖ ^ 2 / t)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      linarith
    _ = _ := by
      rw [show -(ε / 2) * ‖x‖ ^ 2 / t = -((ε / 2) / t) * ‖x‖ ^ 2 by ring,
        Real.exp_add]
      ring

/-- The spatial kernel mass stays bounded near zero: the two Gaussian mass
factors cancel exactly. Unlike the long-time `C/t` bound, this bound is nonsingular. -/
theorem exists_frontRemainderKernel_allTime_integral_norm_bound :
    ∃ C > 0, ∃ κ > 0, ∀ (t : NNReal), 0 < t →
      (∫ x : ℝ^m, ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖) ≤ C * Real.exp (κ * t) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, ν, hν, hb⟩ :=
    exists_frontRemainderKernel_allTime_gaussian_bound (m := m) f D c φ h₁ h₂ ψ h₃
  let p : ℝ := m / 2
  refine ⟨M * (Real.pi / μ) ^ p * (Real.pi / ν) ^ p, by positivity, κ, hκ, ?_⟩
  intro t ht
  have hbt : 0 < ν / (t : ℝ) := div_pos hν ht
  calc
    _ ≤ ∫ x : ℝ^m, (M * (Real.pi / (μ * t)) ^ p * Real.exp (κ * t)) *
        Real.exp (-(ν / t) * ‖x‖ ^ 2) := by
      exact integral_mono
        (integrable_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht).norm
        ((integrable_gaussian_norm hbt).const_mul _) (hb t ht)
    _ = (M * (Real.pi / (μ * t)) ^ p * Real.exp (κ * t)) *
        (Real.pi / (ν / t)) ^ p := by
      rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hbt,
        finrank_euclideanSpace_fin]
    _ = _ := by
      rw [gaussian_mass_scaling (t := (t : ℝ)) hμ ht,
        show Real.pi / (ν / (t : ℝ)) = (Real.pi / ν) * t by field_simp,
        Real.mul_rpow (by positivity) (show 0 ≤ (t : ℝ) from ht.le)]
      calc
        _ = (M * (Real.pi / μ) ^ p * (Real.pi / ν) ^ p * Real.exp (κ * t)) *
            ((t : ℝ) ^ (-p) * (t : ℝ) ^ p) := by ring
        _ = _ := by rw [← Real.rpow_add (show 0 < (t : ℝ) from ht)]; simp

include h₃ in
/-- The full normalized kernel has an exponentially bounded spatial mass,
including as time approaches zero. This controls absolute spatial integrals,
not only the norm of the associated convolution operator. -/
theorem exists_frontFourierKernel_allTime_integral_norm_bound :
    ∃ C > 0, ∃ κ > 0, ∀ (t : NNReal), 0 < t →
      (∫ x : ℝ^m, ‖frontFourierKernel f D c φ h₁ h₂ t x‖) ≤ C * Real.exp (κ * t) := by
  obtain ⟨C, hC, κ, hκ, hb⟩ :=
    exists_frontRemainderKernel_allTime_integral_norm_bound (m := m) f D c φ h₁ h₂ ψ h₃
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  let N : ℝ := ((2 * Real.pi) ^ m)⁻¹
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨‖P‖ + N * C, by positivity, κ, hκ, ?_⟩
  intro t ht
  have hpos : 0 < (4 * d_perp D φ ψ * (t : ℝ))⁻¹ := by
    have := h₃.transverse_low_wavenumber
    positivity
  have hG : Integrable (fun x : ℝ^m ↦ gaussianDensity (4 * d_perp D φ ψ * t)⁻¹ x * ‖P‖) :=
    (integrable_gaussianDensity hpos).mul_const _
  have hR : Integrable (fun x : ℝ^m ↦ N * ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖) :=
    (integrable_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht).norm.const_mul N
  have hpoint (x : ℝ^m) : ‖frontFourierKernel f D c φ h₁ h₂ t x‖ ≤
      gaussianDensity (4 * d_perp D φ ψ * t)⁻¹ x * ‖P‖ +
        N * ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ := by
    rw [frontFourierKernel_decomposition f D c φ h₁ h₂ ψ h₃ t ht x]
    exact (norm_add_le _ _).trans_eq (by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (gaussianDensity_nonneg hpos x), abs_of_pos hN])
  have hexp : 1 ≤ Real.exp (κ * t) := Real.one_le_exp (mul_nonneg hκ.le t.2)
  calc
    _ ≤ ∫ x : ℝ^m, gaussianDensity (4 * d_perp D φ ψ * t)⁻¹ x * ‖P‖ +
        N * ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ :=
      integral_mono (integrable_frontFourierKernel f D c φ h₁ h₂ ψ h₃ t ht).norm (hG.add hR) hpoint
    _ = ‖P‖ + N * ∫ x : ℝ^m, ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ := by
      rw [integral_add hG hR, integral_mul_const, integral_gaussianDensity hpos, one_mul, integral_const_mul]
    _ ≤ ‖P‖ + N * (C * Real.exp (κ * t)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb t ht) hN.le)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hexp (norm_nonneg P)]

local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

/-- The remainder convolution has an exponential bound with no zero-time singularity. -/
theorem exists_frontRemainderConvolution_allTime_bound :
    ∃ C > 0, ∃ κ > 0, ∀ (t : NNReal) (ht : 0 < t),
      ‖frontRemainderConvolutionCLM (m := m) f D c φ h₁ h₂ ψ h₃ t ht‖ ≤ C * Real.exp (κ * t) := by
  obtain ⟨C, hC, κ, hκ, hb⟩ :=
    exists_frontRemainderKernel_allTime_integral_norm_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨((2 * Real.pi) ^ m)⁻¹ * C, by positivity, κ, hκ, ?_⟩
  intro t ht
  exact (norm_frontRemainderConvolutionCLM_le f D c φ h₁ h₂ ψ h₃ t ht).trans
    ((mul_le_mul_of_nonneg_left (hb t ht) (by positivity)).trans_eq (by ring))

/-- The full Fourier convolution, before semigroup identification, is locally
uniformly bounded down to time zero. -/
theorem exists_frontFourierConvolution_allTime_bound :
    ∃ C > 0, ∃ κ > 0, ∀ (t : NNReal) (ht : 0 < t),
      ‖frontFourierConvolutionCLM (m := m) f D c φ h₁ h₂ ψ h₃ t ht‖ ≤ C * Real.exp (κ * t) := by
  obtain ⟨C, hC, κ, hκ, hb⟩ :=
    exists_frontRemainderConvolution_allTime_bound (m := m) f D c φ h₁ h₂ ψ h₃
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  refine ⟨‖P‖ + C, by positivity, κ, hκ, ?_⟩
  intro t ht
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [frontFourierConvolutionCLM_decomposition]
  have hheat : ‖frontCriticalHeatEvolution f D c φ ψ h₃ t v‖ ≤ ‖P‖ * ‖v‖ :=
    (norm_heatFlowBUC_le _ _ _).trans (BUC.norm_postcompCLM_apply_le P v)
  have hR := ((frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg v))
  have hexp : 1 ≤ Real.exp (κ * t) := Real.one_le_exp (mul_nonneg hκ.le t.2)
  calc
    _ ≤ ‖frontCriticalHeatEvolution f D c φ ψ h₃ t v‖ +
        ‖frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v‖ := norm_add_le _ _
    _ ≤ ‖P‖ * ‖v‖ + (C * Real.exp (κ * t)) * ‖v‖ := add_le_add hheat hR
    _ ≤ (‖P‖ + C) * Real.exp (κ * t) * ‖v‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg (norm_nonneg P) (norm_nonneg v))]

end

end Planarwave
