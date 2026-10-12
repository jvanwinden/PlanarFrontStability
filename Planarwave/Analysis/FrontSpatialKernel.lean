/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDiffusionKernel
import all Planarwave.Analysis.FrontSpatialFourierDuhamel

/-!
# The spatial evolution's convolution Volterra equation

The explicit principal Gaussian kernel acts on the slices of every actual
spatial BUC datum as the independently defined principal semigroup. Transport
the actual full spatial Duhamel equation through the bounded slicing map to
obtain its convolution form in the full iterated BUC norm, not just pointwise.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]

local instance : NormedAddCommGroup (BUC (ℝ^(d - 1)) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^(d - 1)) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^(d - 1)) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

/-- Convolution with the principal kernel equals the actual spatial principal
semigroup on every spatial BUC datum, with no integrability assumption on the datum. -/
theorem spatialDiffusionC0Semigroup_eq_kernelConvolution (hd : 2 ≤ d)
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c : ℝ) (t : NNReal) (ht : 0 < t) (v : BUC (ℝ^d) (ℂ^n)) :
    spatialSlices hd (spatialDiffusionC0Semigroup D hD (frontSpatialDrift hd c) t v) =
      operatorConvolution (μ := volume) (frontDiffusionKernel D hD c t) (spatialSlices hd v) := by
  apply BUC.ext
  intro y
  rw [operatorConvolution_apply (continuous_frontDiffusionKernel D hD c t)
    (integrable_frontDiffusionKernel D hD c hDinj t ht)]
  have hsource : (∫ x : ℝ^(d - 1), frontDiffusionKernel D hD c t x (spatialSlices hd v (y - x))) =
      ∫ y' : ℝ^(d - 1), frontDiffusionKernel D hD c t (y - y') (spatialSlices hd v y') := by
    simpa only [sub_sub_cancel] using!
      (integral_sub_left_eq_self (fun x : ℝ^(d - 1) ↦
        frontDiffusionKernel D hD c t x (spatialSlices hd v (y - x))) volume y).symm
  rw [hsource]
  simp_rw [frontDiffusionKernel_eq_fourierIntegral D hD c hDinj t ht]
  rw [integral_smul]
  exact spatialDiffusionC0Semigroup_eq_fourierIntegral hd D hD hDinj c t ht v y

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (hd : 2 ≤ d)

/-- The actual spatial forcing becomes principal kernel convolution with the
longitudinal reaction multiplication on spatial slices. -/
theorem spatialSlices_principal_reaction_convolution (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^d) (ℂ^n)) :
    spatialSlices hd (spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c) t
      (frontSpatialReactionMultiplication f D c φ h₁ h₂ hd v)) =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t)
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂) (spatialSlices hd v)) := by
  rw [spatialDiffusionC0Semigroup_eq_kernelConvolution hd D h₁.positive h₁.kernel c t ht,
    spatialSlices_frontReaction f D c φ h₁ h₂ hd]

/-- The independently defined full spatial semigroup satisfies the convolution
Volterra equation as an equality in the iterated BUC Banach space. -/
theorem frontSpatialC0Semigroup_kernel_volterra (t : NNReal) (ht : 0 < t)
    (v : BUC (ℝ^d) (ℂ^n)) :
    spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) (spatialSlices hd v) +
      ∫ r in 0..(t : ℝ), operatorConvolution (μ := volume)
        (frontDiffusionKernel D h₁.positive c ((t : ℝ) - r).toNNReal)
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
          (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r))) := by
  let S : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) :=
    spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)
  let T : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) := frontSpatialC0Semigroup f D c φ h₁ h₂ hd
  let B : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n) :=
    frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
  let U : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^(d - 1)) (BUC ℝ (ℂ^n)) := spatialSlicesCLM ℂ hd
  have hc : Continuous (fun r : ℝ ↦ S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r)) :=
    continuous_duhamel_two_semigroups S T B v t
  have hm := congrArg U (frontSpatialC0Semigroup_mild f D c φ h₁ h₂ hd v t.2)
  change U (T.realOrbit v t) = U (S.realOrbit v t + S.duhamel (fun r ↦ B (T.realOrbit v r)) t) at hm
  rw [map_add, C0Semigroup.duhamel, ← U.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)] at hm
  have hfree : U (S.realOrbit v t) =
      operatorConvolution (μ := volume) (frontDiffusionKernel D h₁.positive c t) (spatialSlices hd v) := by
    simpa only [U, S, spatialSlicesCLM_apply, C0Semigroup.realOrbit_coe] using!
      spatialDiffusionC0Semigroup_eq_kernelConvolution hd D h₁.positive h₁.kernel c t ht v
  have htime : (∫ r in 0..(t : ℝ), U (S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r))) =
      ∫ r in 0..(t : ℝ), operatorConvolution (μ := volume)
        (frontDiffusionKernel D h₁.positive c ((t : ℝ) - r).toNNReal)
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
          (spatialSlices hd (T.realOrbit v r))) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (show 0 ≤ (t : ℝ) from t.2)
    intro r hr
    exact spatialSlices_principal_reaction_convolution f D c φ h₁ h₂ hd _
      (Real.toNNReal_pos.mpr (sub_pos.mpr hr.2)) (T.realOrbit v r)
  rw [hfree, htime] at hm
  simpa only [U, T, spatialSlicesCLM_apply, C0Semigroup.realOrbit_coe] using! hm

/-- Time integrability of the actual convolution forcing in the full BUC norm. -/
theorem intervalIntegrable_frontSpatial_kernel_forcing (t : NNReal)
    (v : BUC (ℝ^d) (ℂ^n)) :
    IntervalIntegrable (fun r : ℝ ↦ operatorConvolution (μ := volume)
      (frontDiffusionKernel D h₁.positive c ((t : ℝ) - r).toNNReal)
      (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
        (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r)))) volume 0 t := by
  let S : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) :=
    spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)
  let T : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) := frontSpatialC0Semigroup f D c φ h₁ h₂ hd
  let B : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n) :=
    frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
  let U : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^(d - 1)) (BUC ℝ (ℂ^n)) := spatialSlicesCLM ℂ hd
  have hc : Continuous (fun r : ℝ ↦ S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r)) :=
    continuous_duhamel_two_semigroups S T B v t
  have hi : IntervalIntegrable (fun r : ℝ ↦
      U (S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r))) volume 0 t :=
    (U.continuous.comp hc).intervalIntegrable 0 (t : ℝ)
  apply hi.congr_uIoo
  intro r hr
  have hr' : r ∈ Ioo 0 (t : ℝ) := uIoo_of_le (show 0 ≤ (t : ℝ) from t.2) ▸ hr
  exact spatialSlices_principal_reaction_convolution f D c φ h₁ h₂ hd _
    (Real.toNNReal_pos.mpr (sub_pos.mpr hr'.2)) (T.realOrbit v r)

end

end Planarwave
