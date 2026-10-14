/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontKernelVolterra
import all Planarwave.Analysis.FrontFourierShortTime
import Planarwave.Analysis.BUCConvolutionComposition

/-!
# The spatial Volterra forcing on bounded initial data

Apply the ordered spatial Fubini theorem to the actual principal and full
Fourier kernels. No spatial integrability of the datum is needed. The absolute
double integral is uniformly bounded over the open Duhamel time interval.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ}

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n)) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- The actual kernel product on bounded initial data, before spatial integration. -/
def frontBoundedKernelIntegrand (s r : NNReal) (v : BUC (ℝ^m) (BUC ℝ (ℂ^n)))
    (p : (ℝ^m) × (ℝ^m)) : BUC (ℝ^m) (BUC ℝ (ℂ^n)) :=
  orderedConvolutionIntegrand (frontDiffusionKernel D h₁.positive c s)
    (frontFourierKernel f D c φ h₁ h₂ r) (frontReactionMultiplication f D c φ h₁ h₂) v p

variable (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The double spatial integral in the kernel equation, evaluated on general
bounded data, is exactly the expected convolution forcing. -/
theorem frontKernel_forcing_on_bounded_data (s r : NNReal) (hs : 0 < s) (hr : 0 < r)
    (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (z : ℝ^m) :
    (∫ x : ℝ^m, ∫ y : ℝ^m, frontDiffusionKernel D h₁.positive c s y
      (frontReactionMultiplication f D c φ h₁ h₂
        (frontFourierKernel f D c φ h₁ h₂ r (x - y) (v (z - x))))) =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c s)
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
          (frontFourierConvolutionCLM f D c φ h₁ h₂ ψ h₃ r hr v)) z :=
  integral_orderedConvolution_apply
    (continuous_frontDiffusionKernel D h₁.positive c s)
    (integrable_frontDiffusionKernel D h₁.positive c h₁.kernel s hs)
    (continuous_frontFourierKernel f D c φ h₁ h₂ ψ h₃ r hr)
    (integrable_frontFourierKernel f D c φ h₁ h₂ ψ h₃ r hr) _ v z

include h₃ in
/-- The absolute double spatial integral has a bound uniform in the time split,
including as either lag approaches zero. This is the spatial majorant for
time-space Fubini, not an assumption that Fubini is already valid in time. -/
theorem exists_frontBoundedKernelIntegrand_integral_norm_bound :
    ∃ C > 0, ∃ κ > 0, ∀ (t : ℝ), 0 ≤ t → ∀ r ∈ Ioo 0 t,
      ∀ v : BUC (ℝ^m) (BUC ℝ (ℂ^n)),
        (∫ x : ℝ^m, ∫ y : ℝ^m,
          ‖frontBoundedKernelIntegrand f D c φ h₁ h₂ (t-r).toNNReal r.toNNReal v (x, y)‖) ≤
            C * Real.exp (κ * t) * ‖v‖ := by
  obtain ⟨C, hC, κ, hκ, hfull⟩ :=
    exists_frontFourierKernel_allTime_integral_norm_bound (m := m) f D c φ h₁ h₂ ψ h₃
  let A : ℝ := ‖(diffusionBUCCoordinatesEquiv D h₁.positive).toContinuousLinearMap‖ *
    (n * ‖(diffusionBUCCoordinatesEquiv D h₁.positive).symm.toContinuousLinearMap‖)
  let B := frontReactionMultiplication f D c φ h₁ h₂
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(A + 1) * C * (‖B‖ + 1), by positivity, κ, hκ, ?_⟩
  intro t ht r hr v
  have hs : 0 < (t-r).toNNReal := Real.toNNReal_pos.mpr (sub_pos.mpr hr.2)
  have hrr : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr.1
  have hfree : (∫ x : ℝ^m, ‖frontDiffusionKernel D h₁.positive c (t-r).toNNReal x‖) ≤ A :=
    integral_norm_frontDiffusionKernel_le D h₁.positive c h₁.kernel _ hs
  have hfull' : (∫ x : ℝ^m, ‖frontFourierKernel f D c φ h₁ h₂ r.toNNReal x‖) ≤
      C * Real.exp (κ * t) := by
    apply (hfull _ hrr).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    rw [Real.coe_toNNReal _ hr.1.le]
    exact mul_le_mul_of_nonneg_left hr.2.le hκ.le
  have hh := integral_norm_orderedConvolutionIntegrand_le
    (continuous_frontDiffusionKernel (m := m) D h₁.positive c (t-r).toNNReal)
    (integrable_frontDiffusionKernel D h₁.positive c h₁.kernel _ hs)
    (continuous_frontFourierKernel f D c φ h₁ h₂ ψ h₃ _ hrr)
    (integrable_frontFourierKernel f D c φ h₁ h₂ ψ h₃ _ hrr) B v
  apply hh.trans
  calc
    _ ≤ (A * (C * Real.exp (κ * t))) * (‖B‖ * ‖v‖) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hfree hfull' (integral_nonneg fun _ ↦ norm_nonneg _) hA
    _ ≤ ((A + 1) * (C * Real.exp (κ * t))) * ((‖B‖ + 1) * ‖v‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)
      · positivity
      · positivity
    _ = _ := by ring

end

end Planarwave
