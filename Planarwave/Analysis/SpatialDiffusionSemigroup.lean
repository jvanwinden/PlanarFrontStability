/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionEigenbasis
import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional

/-!
# The full spatial matrix diffusion semigroup

Diagonalize the actual positive diffusion matrix and evolve each component by
the full-dimensional Gaussian heat semigroup with the same drift. Unlike the
longitudinal construction, there is no transverse Fourier parameter here.
The generator calculation is in the BUC norm, on twice BUC differentiable data
expressed in the diffusion eigenbasis.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

/-- The same diffusion eigenbasis acting on full spatial BUC functions. -/
def spatialDiffusionBUCCoordinatesEquiv (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) :
    (Fin n → BUC E ℂ) ≃L[ℂ] BUC E (ℂ^n) :=
  (BUC.piCLE (α := E) (𝕜 := ℂ) (X := fun _ : Fin n ↦ ℂ)).symm.trans
    (BUC.postcompCLE (diffusionCoordinatesEquiv D hD))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem spatialDiffusionBUCCoordinatesEquiv_apply (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (v : Fin n → BUC E ℂ) (x : E) :
    spatialDiffusionBUCCoordinatesEquiv D hD v x = diffusionCoordinatesEquiv D hD (fun i ↦ v i x) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem spatialDiffusionBUCCoordinatesEquiv_symm_apply (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (v : BUC E (ℂ^n)) (i : Fin n) (x : E) :
    (spatialDiffusionBUCCoordinatesEquiv D hD).symm v i x =
      (diffusionCoordinatesEquiv D hD).symm (v x) i := rfl

variable [Nontrivial (ℝ^n)]

/-- Principal matrix diffusion and drift on the full spatial BUC space. -/
def spatialDiffusionC0Semigroup (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (b : E) :
    C0Semigroup ℂ (BUC E (ℂ^n)) :=
  (C0Semigroup.pi fun i : Fin n ↦
    complexConvectiveHeatC0Semigroup (diffusionEigenvalues D hD i) (diffusionEigenvalues_nonneg D hD i) b).conjugate
      (spatialDiffusionBUCCoordinatesEquiv D hD)

/-- Explicit Gaussian formula for each eigenvector coordinate. -/
theorem spatialDiffusionC0Semigroup_apply (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (b : E) (t : NNReal) (v : BUC E (ℂ^n)) :
    spatialDiffusionC0Semigroup D hD b t v = spatialDiffusionBUCCoordinatesEquiv D hD
      (fun i ↦ convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t b
        ((spatialDiffusionBUCCoordinatesEquiv D hD).symm v i)) := rfl

/-- The full principal evolution is uniformly bounded by the fixed eigenbasis condition number. -/
theorem norm_spatialDiffusionC0Semigroup_le (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (b : E) (t : NNReal) :
    ‖spatialDiffusionC0Semigroup D hD b t‖ ≤
      ‖(spatialDiffusionBUCCoordinatesEquiv (E := E) D hD).toContinuousLinearMap‖ *
        ‖(spatialDiffusionBUCCoordinatesEquiv (E := E) D hD).symm.toContinuousLinearMap‖ := by
  have hdiag : ‖(C0Semigroup.pi fun i : Fin n ↦
      complexConvectiveHeatC0Semigroup (diffusionEigenvalues D hD i)
        (diffusionEigenvalues_nonneg D hD i) b) t‖ ≤ 1 :=
    C0Semigroup.norm_pi_le _ t zero_le_one (fun i ↦ norm_complexConvectiveHeatOperator_le _ _ _)
  simpa only [mul_one, spatialDiffusionC0Semigroup] using!
    (C0Semigroup.norm_conjugate_le_of_norm_le _ (spatialDiffusionBUCCoordinatesEquiv D hD) t hdiag)

/-- A strictly positive uniform principal-semigroup bound, independent of drift and time. -/
theorem exists_uniform_spatialDiffusion_bound (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) :
    ∃ M > 0, ∀ (b : E) (t : NNReal), ‖spatialDiffusionC0Semigroup D hD b t‖ ≤ M := by
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  refine ⟨max (‖J.toContinuousLinearMap‖ * ‖J.symm.toContinuousLinearMap‖) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro b t
  exact (norm_spatialDiffusionC0Semigroup_le D hD b t).trans (le_max_left _ _)

/-- Generator action after returning from the scalar diffusion coordinates.
The scalar terms are the proved differential operators `aᵢ Δ + b · ∇`. -/
theorem spatialDiffusionC0Semigroup_hasGeneratorAt
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (b : E)
    (v : Fin n → BUC E ℂ) (g : Fin n → BUC E (E →L[ℝ] ℂ))
    (h : Fin n → BUC E (E →L[ℝ] E →L[ℝ] ℂ))
    (hg : ∀ i x, HasFDerivAt (v i) (g i x) x) (hh : ∀ i x, HasFDerivAt (g i) (h i x) x) :
    (spatialDiffusionC0Semigroup D hD b).HasGeneratorAt
      (spatialDiffusionBUCCoordinatesEquiv D hD v)
      (spatialDiffusionBUCCoordinatesEquiv D hD
        (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D hD i) b (g i) (h i))) := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  have hd : HasDerivWithinAt
      (fun t : ℝ ↦ fun i ↦ convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t b (v i))
      (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D hD i) b (g i) (h i)) (Ici 0) 0 :=
    hasDerivWithinAt_pi.mpr fun i ↦
      hasDerivWithinAt_convectiveHeatFlowBUC_zero_fderiv (hμ.trans_le (hμle i)) b (v i) (g i) (h i) (hg i) (hh i)
  have hj := (J.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hd
  apply hj.congr
  · intro t ht
    change spatialDiffusionC0Semigroup D hD b t.toNNReal (J v) = _
    rw [spatialDiffusionC0Semigroup_apply, show (spatialDiffusionBUCCoordinatesEquiv D hD).symm (J v) = v
      from J.symm_apply_apply v, Real.coe_toNNReal _ ht]
    rfl
  · simp [C0Semigroup.realOrbit, J]

end

end Planarwave
