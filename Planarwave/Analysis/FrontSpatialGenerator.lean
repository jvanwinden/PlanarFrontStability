/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSpatialSemigroup

/-!
# Spatial diffusion generator in the original coordinates

Return from diffusion eigenvector coordinates and identify the generator
pointwise with matrix diffusion and drift. The retained coordinate identity
is used when identifying the full linearized differential operator.
-/

open Filter Set Topology
open scoped Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

section Regularity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two continuous specified Fréchet derivatives give `C²` regularity. -/
theorem contDiff_two_of_buc_fderivatives (v : BUC E F) (g : BUC E (E →L[ℝ] F))
    (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hg : ∀ x, HasFDerivAt v (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) :
    ContDiff ℝ 2 (v : E → F) := by
  have hvg : fderiv ℝ v = g := funext fun x ↦ (hg x).fderiv
  have hgh : fderiv ℝ g = h := funext fun x ↦ (hh x).fderiv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun x ↦ (hg x).differentiableAt, by simp, ?_⟩
  rw [hvg, contDiff_one_iff_fderiv, hgh]
  exact ⟨fun x ↦ (hh x).differentiableAt, h.continuous⟩

end Regularity

variable {n : ℕ}

section Principal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- In original state coordinates the diagonal generator is precisely matrix
diffusion plus the common drift. -/
theorem spatialDiffusionGenerator_coordinates (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (b : E) (v : Fin n → BUC E ℂ) (g : Fin n → BUC E (E →L[ℝ] ℂ))
    (h : Fin n → BUC E (E →L[ℝ] E →L[ℝ] ℂ))
    (hg : ∀ i x, HasFDerivAt (v i) (g i x) x) (hh : ∀ i x, HasFDerivAt (g i) (h i x) x) (x : E) :
    spatialDiffusionBUCCoordinatesEquiv D hD
        (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D hD i) b (g i) (h i)) x =
      frontComplexifiedDiffusion D (Δ (spatialDiffusionBUCCoordinatesEquiv D hD v : E → ℂ^n) x) +
        fderiv ℝ (spatialDiffusionBUCCoordinatesEquiv D hD v) x b := by
  let J := diffusionCoordinatesEquiv D hD
  let u : E → Fin n → ℂ := fun y i ↦ v i y
  have hu : ContDiff ℝ 2 u := contDiff_pi.mpr fun i ↦ contDiff_two_of_buc_fderivatives (v i) (g i) (h i) (hg i) (hh i)
  have hΔ : Δ (spatialDiffusionBUCCoordinatesEquiv D hD v : E → ℂ^n) x = J (Δ u x) := by
    exact hu.contDiffAt.laplacian_CLM_comp_left (l := J.toContinuousLinearMap.restrictScalars ℝ)
  have hΔi (i : Fin n) : Δ (v i : E → ℂ) x = (Δ u x) i := by
    exact hu.contDiffAt.laplacian_CLM_comp_left
      (l := (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)
  have hderiv := (J.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
    (hasFDerivAt_pi.mpr (fun i ↦ hg i x))
  have hd : fderiv ℝ (spatialDiffusionBUCCoordinatesEquiv D hD v) x b =
      J (fun i ↦ g i x b) := by
    exact congrArg (fun L : E →L[ℝ] ℂ^n ↦ L b) hderiv.fderiv
  rw [hΔ, hd, complexifiedDiffusion_coordinates]
  rw [← J.map_add]
  change J (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D hD i) b (g i) (h i) x) = _
  congr 1
  funext i
  rw [convectiveGeneratorBUC_apply _ _ (v i) _ _ (hg i) (hh i), hΔi, (hg i x).fderiv]
  simp [Complex.real_smul]

end Principal

end

end Planarwave
