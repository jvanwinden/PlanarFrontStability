/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontKernelDecay
import Planarwave.Analysis.BUCOperatorConvolution
import Planarwave.Analysis.BUCSlices

/-!
# The bounded remainder convolution

The actual Fourier remainder kernel defines a bounded operator on transverse
BUC functions taking values in longitudinal BUC. We include the inverse Fourier
normalization and obtain its `O(1/t)` operator bound. No identity with the full
spatial semigroup is assumed in this construction.
-/

open MeasureTheory

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  (SeminormedAddGroup.toESeminormedAddMonoid
    (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))).toContinuousENorm

/-- The normalized spatial convolution of the Fourier remainder kernel. -/
def frontRemainderConvolutionCLM (t : NNReal) (ht : 0 < t) :
    BUC (ℝ^m) (BUC ℝ (ℂ^n)) →L[ℂ] BUC (ℝ^m) (BUC ℝ (ℂ^n)) :=
  ((2 * Real.pi) ^ m)⁻¹ • operatorConvolutionCLM
    (continuous_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht)
    (integrable_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht)

/-- Evaluation at the transverse variable gives the paper's outer integral. -/
theorem frontRemainderConvolutionCLM_apply (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (y : ℝ^m) :
    frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v y =
      ((2 * Real.pi) ^ m)⁻¹ • ∫ x : ℝ^m, frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x (v (y - x)) := by
  rw [frontRemainderConvolutionCLM, smul_apply, BUC.smul_apply,
    operatorConvolutionCLM_apply, operatorConvolution_apply
      (continuous_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht)
      (integrable_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht)]

/-- The convolution norm is bounded by the normalized spatial mass of the kernel. -/
theorem norm_frontRemainderConvolutionCLM_le (t : NNReal) (ht : 0 < t) :
    ‖frontRemainderConvolutionCLM (m := m) f D c φ h₁ h₂ ψ h₃ t ht‖ ≤
      ((2 * Real.pi) ^ m)⁻¹ * ∫ x : ℝ^m, ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ := by
  have hn (a : ℝ) (A : BUC (ℝ^m) (BUC ℝ (ℂ^n)) →L[ℂ] BUC (ℝ^m) (BUC ℝ (ℂ^n))) :
      ‖a • A‖ = ‖a‖ * ‖A‖ := norm_smul a A
  rw [frontRemainderConvolutionCLM, hn, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (norm_operatorConvolutionCLM_le
      (continuous_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht)
      (integrable_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t ht)) (by positivity)

/-- The `1/t` bound for the normalized, genuinely constructed remainder convolution. -/
theorem exists_frontRemainderConvolutionCLM_decay_bound :
    ∃ C > 0, ∀ (t : NNReal) (ht : 0 < t), 1 ≤ t →
      ‖frontRemainderConvolutionCLM (m := m) f D c φ h₁ h₂ ψ h₃ t ht‖ ≤ C / t := by
  obtain ⟨C, hC, hb⟩ := exists_frontRemainderKernel_integral_norm_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨((2 * Real.pi) ^ m)⁻¹ * C, by positivity, ?_⟩
  intro t ht htone
  exact (norm_frontRemainderConvolutionCLM_le f D c φ h₁ h₂ ψ h₃ t ht).trans
    ((mul_le_mul_of_nonneg_left (hb t htone) (by positivity)).trans_eq (by ring))

/-- The uniform pointwise bound on the convolution of longitudinal slices. -/
theorem exists_frontRemainderConvolutionCLM_pointwise_decay_bound :
    ∃ C > 0, ∀ (t : NNReal) (ht : 0 < t), 1 ≤ t →
      ∀ (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (y : ℝ^m) (z : ℝ),
      ‖frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht v y z‖ ≤ (C / t) * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := exists_frontRemainderConvolutionCLM_decay_bound (m := m) f D c φ h₁ h₂ ψ h₃
  refine ⟨C, hC, ?_⟩
  intro t ht htone v y z
  exact (BUC.norm_apply_le _ z).trans ((BUC.norm_apply_le _ y).trans
    (((frontRemainderConvolutionCLM f D c φ h₁ h₂ ψ h₃ t ht).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb t ht htone) (norm_nonneg v))))

end

end Planarwave
