/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.SpatialHeatFourier
import all Planarwave.Analysis.FrontSpatialSemigroup
import Planarwave.Analysis.DiagonalHeatFourier

/-!
# Fourier representation of the actual spatial principal semigroup

The matrix diffusion semigroup constructed independently in spatial BUC equals
the iterated transverse Fourier integral of the longitudinal principal pencil.
This is the principal-evolution step in Section 3's first Fourier formula; the
bounded reaction perturbation is not yet included in this identification.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {d n : ℕ}

/-- Slicing and the fixed diffusion eigenbasis commute. -/
theorem spatialSlices_diffusionCoordinates (hd : 2 ≤ d) (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (v : Fin n → BUC (ℝ^d) ℂ) (y : ℝ^(d - 1)) :
    spatialSlices hd (spatialDiffusionBUCCoordinatesEquiv D hD v) y =
      diffusionBUCCoordinatesEquiv D hD (fun i ↦ spatialSlices hd (v i) y) := by
  apply BUC.ext
  intro z
  rfl

/-- The inverse diffusion eigenbasis also commutes with spatial slicing. -/
theorem spatialSlices_diffusionCoordinates_symm (hd : 2 ≤ d) (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (v : BUC (ℝ^d) (ℂ^n)) (y : ℝ^(d - 1)) (i : Fin n) :
    (diffusionBUCCoordinatesEquiv D hD).symm (spatialSlices hd v y) i =
      spatialSlices hd ((spatialDiffusionBUCCoordinatesEquiv D hD).symm v i) y := by
  apply BUC.ext
  intro z
  rfl

variable [Nontrivial (ℝ^n)]

/-- The full spatial principal semigroup, factored in its actual diffusion
coordinates into transverse and longitudinal Gaussian evolutions. -/
theorem spatialDiffusionC0Semigroup_slices (hd : 2 ≤ d) (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (c : ℝ) (t : NNReal) (v : BUC (ℝ^d) (ℂ^n)) (y : ℝ^(d - 1)) :
    spatialSlices hd (spatialDiffusionC0Semigroup D hD (frontSpatialDrift hd c) t v) y =
      diffusionBUCCoordinatesEquiv D hD (fun i ↦
        heatFlowBUC (diffusionEigenvalues D hD i) t
          (BUC.postcompCLM (convectiveHeatOperator (E := ℝ) (F := ℂ)
            (diffusionEigenvalues D hD i) t c)
            (spatialSlices hd ((spatialDiffusionBUCCoordinatesEquiv D hD).symm v i))) y) := by
  rw [spatialDiffusionC0Semigroup_apply, spatialSlices_diffusionCoordinates]
  congr 1
  funext i
  exact congrArg (fun w ↦ w y) (spatialSlices_convectiveHeat hd
    (diffusionEigenvalues D hD i) t c ((spatialDiffusionBUCCoordinatesEquiv D hD).symm v i))

/-- The first Fourier formula in Section 3 for the independent principal matrix
evolution, before adding the bounded reaction coefficient. -/
theorem spatialDiffusionC0Semigroup_eq_fourierIntegral (hd : 2 ≤ d)
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c : ℝ) (t : NNReal) (ht : 0 < t) (v : BUC (ℝ^d) (ℂ^n)) (y : ℝ^(d - 1)) :
    spatialSlices hd (spatialDiffusionC0Semigroup D hD (frontSpatialDrift hd c) t v) y =
      ((2 * Real.pi) ^ (d - 1))⁻¹ • ∫ y' : ℝ^(d - 1), ∫ ξ : ℝ^(d - 1),
        Complex.exp (Complex.I * (⟪ξ, y - y'⟫ : ℂ)) •
          (frontDiffusionC0Semigroup D hD c (‖ξ‖ ^ 2) t (spatialSlices hd v y')) := by
  let a : Fin n → ℝ := diffusionEigenvalues D hD
  let u : Fin n → BUC (ℝ^(d - 1)) (BUC ℝ ℂ) := fun i ↦
    BUC.postcompCLM (convectiveHeatOperator (E := ℝ) (F := ℂ) (a i) t c)
      (spatialSlices hd ((spatialDiffusionBUCCoordinatesEquiv D hD).symm v i))
  let J : (Fin n → BUC ℝ ℂ) →L[ℂ] BUC ℝ (ℂ^n) :=
    (diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  have ha : ∀ i, 0 < a i := fun i ↦ hμ.trans_le (hμle i)
  have hfourier : J (fun i ↦ heatFlowBUC (a i) t (u i) y) =
      ((2 * Real.pi) ^ (d - 1))⁻¹ • ∫ y' : ℝ^(d - 1), ∫ ξ : ℝ^(d - 1),
        Complex.exp (Complex.I * (⟪ξ, y - y'⟫ : ℂ)) •
          J (fun i ↦ Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • u i y') := by
    simpa only [finrank_euclideanSpace_fin] using!
      diagonal_heatFlowBUC_eq_fourierIntegral a ha ht u J y
  have hsymbol (y' ξ : ℝ^(d - 1)) :
      J (fun i ↦ Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) • u i y') =
        frontDiffusionC0Semigroup D hD c (‖ξ‖ ^ 2) t (spatialSlices hd v y') := by
    have he (i : Fin n) : Complex.exp (-((a i * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) =
        (Real.exp ((-‖ξ‖ ^ 2 * a i) * (t : ℝ)) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    simp only [J, frontDiffusionC0Semigroup_apply, frontDiffusionFlowBUC,
      spatialSlices_diffusionCoordinates_symm hd, u, BUC.postcompCLM_apply,
      convectiveHeatOperator_apply, he]
    rfl
  rw [spatialDiffusionC0Semigroup_slices]
  simp only [hsymbol] at hfourier
  simpa only [J, u, a] using! hfourier

end

end Planarwave
