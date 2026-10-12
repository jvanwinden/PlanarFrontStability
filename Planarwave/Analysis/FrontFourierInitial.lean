/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontBoundedDuhamel
import all Planarwave.Analysis.FrontSpatialKernel

/-!
# Initial-value limit of the full Fourier evolution

The reaction contribution is `O(t)` in the full supremum norm. On actual
spatial BUC data, principal-kernel convolution is the independently constructed
diffusion semigroup, which is strongly continuous at zero. Consequently the
full Fourier convolution attains the correct initial data. No strong
continuity assertion on arbitrary iterated-BUC data is made.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n d : ℕ}

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n)) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₃ in
/-- The reaction part tends to zero in the full iterated BUC norm. -/
theorem tendsto_frontFourierConvolution_sub_principal (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) :
    Tendsto (fun t : NNReal ↦
      operatorConvolution (μ := volume) (frontFourierKernel f D c φ h₁ h₂ t) v -
        operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) v)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, κ, _, hb⟩ :=
    exists_frontFourierConvolution_principal_difference_bound (m := m) f D c φ h₁ h₂ ψ h₃
  have hc : Continuous (fun t : NNReal ↦ (t : ℝ) * (C * Real.exp (κ * t) * ‖v‖)) := by fun_prop
  have hlim : Tendsto (fun t : NNReal ↦ (t : ℝ) * (C * Real.exp (κ * t) * ‖v‖))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [NNReal.coe_zero, zero_mul] using!
      (hc.continuousAt (x := (0 : NNReal))).tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hb t ht v

include h₃ in
/-- The Fourier formula has the correct initial value on actual spatial BUC
data, with convergence in the complete spatial supremum norm. -/
theorem tendsto_frontFourierConvolution_spatial_zero (hd : 2 ≤ d) (v : BUC (ℝ^d) (ℂ^n)) :
    Tendsto (fun t : NNReal ↦ operatorConvolution (μ := volume)
      (frontFourierKernel f D c φ h₁ h₂ t) (spatialSlices hd v))
      (𝓝[>] 0) (𝓝 (spatialSlices hd v)) := by
  let S := spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)
  let U := spatialSlicesCLM ℂ (F := ℂ^n) hd
  have hs : Tendsto (fun t : NNReal ↦ U (S t v)) (𝓝[>] 0) (𝓝 (U v)) :=
    (U.continuous.tendsto v).comp ((S.tendsto_zero v).mono_left nhdsWithin_le_nhds)
  have hp : Tendsto (fun t : NNReal ↦ operatorConvolution (μ := volume)
      (frontDiffusionKernel D h₁.positive c t) (spatialSlices hd v))
      (𝓝[>] 0) (𝓝 (spatialSlices hd v)) := by
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact spatialDiffusionC0Semigroup_eq_kernelConvolution hd D h₁.positive h₁.kernel c t ht v
  have hz := tendsto_frontFourierConvolution_sub_principal f D c φ h₁ h₂ ψ h₃ (spatialSlices hd v)
  simpa only [sub_add_cancel, zero_add] using! hz.add hp

end

end Planarwave
