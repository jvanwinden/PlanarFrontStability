/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionSemigroup
import Planarwave.Analysis.DiagonalGaussianConvolution

/-!
# The principal spatial operator kernel

Diagonalize the actual diffusion matrix and retain the longitudinal convective
heat operators. The resulting transverse Gaussian kernel has the exact principal
Fourier symbol. Multiplying that symbol by an integrable frequency amplitude is
spatial convolution with this operator kernel.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ}

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n)) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace

variable (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (c : ℝ)

/-- Each longitudinal heat operator, preceded by its actual diffusion-coordinate projection. -/
def frontDiffusionCoordinateHeat (t : NNReal) (i : Fin n) : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ ℂ :=
  (complexConvectiveHeatOperator (diffusionEigenvalues D hD i) t c).comp
    ((ContinuousLinearMap.proj i).comp (diffusionBUCCoordinatesEquiv D hD).symm.toContinuousLinearMap)

/-- The transverse operator kernel of principal diffusion and longitudinal drift.
Its Fourier interpretation is asserted only at positive time. -/
def frontDiffusionKernel (t : NNReal) (x : ℝ^m) : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  diagonalGaussianKernel (fun i ↦ diffusionEigenvalues D hD i * t)
    (frontDiffusionCoordinateHeat D hD c t) (diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap x

/-- The principal kernel in the explicit diffusion eigenbasis. -/
theorem frontDiffusionKernel_apply (t : NNReal) (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    frontDiffusionKernel D hD c t x v = diffusionBUCCoordinatesEquiv D hD (fun i ↦
      gaussianDensity (4 * (diffusionEigenvalues D hD i * t))⁻¹ x •
        convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t c
          ((diffusionBUCCoordinatesEquiv D hD).symm v i)) := rfl

/-- Spatial continuity in operator norm. -/
theorem continuous_frontDiffusionKernel (t : NNReal) :
    Continuous (frontDiffusionKernel (m := m) D hD c t) :=
  continuous_diagonalGaussianKernel _ _ _

/-- Absolute spatial integrability in operator norm. -/
theorem integrable_frontDiffusionKernel (hDinj : Function.Injective D) [Nontrivial (ℝ^n)]
    (t : NNReal) (ht : 0 < t) : Integrable (frontDiffusionKernel (m := m) D hD c t) := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  exact integrable_diagonalGaussianKernel _ (fun i ↦ mul_pos (hμ.trans_le (hμle i)) ht) _ _

variable [Nontrivial (ℝ^n)]

/-- The kernel's diagonal frequency multiplier is the independently defined principal semigroup. -/
theorem frontDiffusion_gaussian_symbol (t : NNReal) (ξ : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    diffusionBUCCoordinatesEquiv D hD (fun i ↦
      Complex.exp (-((diffusionEigenvalues D hD i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) •
        frontDiffusionCoordinateHeat D hD c t i v) =
      frontDiffusionC0Semigroup D hD c (‖ξ‖ ^ 2) t v := by
  rw [frontDiffusionC0Semigroup_apply, frontDiffusionFlowBUC]
  congr 1
  funext i
  have he : Complex.exp (-((diffusionEigenvalues D hD i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) =
      (Real.exp ((-‖ξ‖ ^ 2 * diffusionEigenvalues D hD i) * (t : ℝ)) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he]
  rfl

/-- Exact normalized inverse Fourier representation of the principal kernel. -/
theorem frontDiffusionKernel_eq_fourierIntegral (hDinj : Function.Injective D)
    (t : NNReal) (ht : 0 < t) (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    frontDiffusionKernel D hD c t x v = ((2 * Real.pi) ^ m)⁻¹ •
      oscillatoryIntegral (fun ξ : ℝ^m ↦ frontDiffusionC0Semigroup D hD c (‖ξ‖ ^ 2) t v) x := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  have he := diagonalGaussianKernel_eq_fourierIntegral
    (fun i ↦ diffusionEigenvalues D hD i * (t : ℝ))
    (fun i ↦ mul_pos (hμ.trans_le (hμle i)) (show 0 < (t : ℝ) from ht))
    (frontDiffusionCoordinateHeat D hD c t) (diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap x v
  simpa only [frontDiffusionKernel, finrank_euclideanSpace_fin,
    ContinuousLinearEquiv.coe_coe, frontDiffusion_gaussian_symbol] using! he

/-- Multiplication by the principal Fourier symbol is spatial convolution with
the actual matrix Gaussian kernel, including the longitudinal heat operators. -/
theorem frontDiffusionKernel_fourier_convolution (hDinj : Function.Injective D)
    (t : NNReal) (ht : 0 < t) {g : ℝ^m → BUC ℝ (ℂ^n)}
    (hg : Continuous g) (hi : Integrable g) (x : ℝ^m) :
    oscillatoryIntegral (fun ξ : ℝ^m ↦ frontDiffusionC0Semigroup D hD c (‖ξ‖ ^ 2) t (g ξ)) x =
      ∫ y : ℝ^m, frontDiffusionKernel D hD c t y (oscillatoryIntegral g (x - y)) := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  have he := diagonalGaussian_fourier_convolution
    (fun i ↦ diffusionEigenvalues D hD i * (t : ℝ))
    (fun i ↦ mul_pos (hμ.trans_le (hμle i)) (show 0 < (t : ℝ) from ht))
    (frontDiffusionCoordinateHeat D hD c t) (diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap hg hi x
  simpa only [frontDiffusionKernel, ContinuousLinearEquiv.coe_coe, frontDiffusion_gaussian_symbol] using! he

omit [Nontrivial (ℝ^n)] in
/-- Each coordinate heat operator costs at most the fixed inverse eigenbasis norm. -/
theorem norm_frontDiffusionCoordinateHeat_le (t : NNReal) (i : Fin n) :
    ‖frontDiffusionCoordinateHeat D hD c t i‖ ≤
      ‖(diffusionBUCCoordinatesEquiv D hD).symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (norm_convectiveHeatFlowBUC_le _ _ _ _).trans
    ((norm_le_pi_norm ((diffusionBUCCoordinatesEquiv D hD).symm v) i).trans
      ((diffusionBUCCoordinatesEquiv D hD).symm.toContinuousLinearMap.le_opNorm v))

/-- The principal spatial kernel has a time-uniform `L¹` operator norm bound.
This is the bound needed at the zero-lag endpoint of spatial-time Fubini. -/
theorem integral_norm_frontDiffusionKernel_le (hDinj : Function.Injective D)
    (t : NNReal) (ht : 0 < t) :
    (∫ x : ℝ^m, ‖frontDiffusionKernel D hD c t x‖) ≤
      ‖(diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap‖ *
        (n * ‖(diffusionBUCCoordinatesEquiv D hD).symm.toContinuousLinearMap‖) := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  have hb : ∀ i, 0 < diffusionEigenvalues D hD i * (t : ℝ) :=
    fun i ↦ mul_pos (hμ.trans_le (hμle i)) ht
  apply (integral_norm_diagonalGaussianKernel_le _ hb
    (frontDiffusionCoordinateHeat D hD c t) (diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑ _ : Fin n, ‖(diffusionBUCCoordinatesEquiv D hD).symm.toContinuousLinearMap‖ :=
      Finset.sum_le_sum fun i _ ↦ norm_frontDiffusionCoordinateHeat_le D hD c t i
    _ = _ := by simp

end

end Planarwave
