/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.CoordinateGaussian
import Planarwave.Analysis.BUCSlices
import Planarwave.Analysis.ConvectiveHeatSemigroup
import Planarwave.Analysis.GaussianHeatKernel

/-!
# Transverse Fourier representation of the spatial scalar heat evolution

Split the independently defined full spatial Gaussian into transverse and
longitudinal coordinates. Fourier inversion is used only for the transverse
Gaussian, leaving the longitudinal convective heat semigroup as its amplitude.
The formulas hold for all BUC data, not merely spatially integrable data.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F]

/-- Full spatial BUC data as a BUC family of longitudinal slices. -/
def spatialSlices (hd : 2 ≤ d) (v : BUC (ℝ^d) F) : BUC (ℝ^(d - 1)) (BUC ℝ F) :=
  BUC.curry (v.comp (coordinateEquiv hd).symm (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous)

@[simp]
theorem spatialSlices_apply (hd : 2 ≤ d) (v : BUC (ℝ^d) F) (y : ℝ^(d - 1)) (z : ℝ) :
    spatialSlices hd v y z = v (full y z) := rfl

/-- Slicing preserves the spatial supremum norm. -/
theorem norm_spatialSlices (hd : 2 ≤ d) (v : BUC (ℝ^d) F) : ‖spatialSlices hd v‖ = ‖v‖ := by
  apply le_antisymm
  · exact (BUC.norm_curry _).le.trans (BUC.norm_comp_le _ _ _)
  · apply (BUC.norm_le (norm_nonneg _)).mpr
    intro x
    have h := (BUC.norm_apply_le (spatialSlices hd v (transverse x)) (horizontal x)).trans
      (BUC.norm_apply_le (spatialSlices hd v) (transverse x))
    simpa only [spatialSlices_apply, full_transverse_horizontal hd] using h

/-- The slicing embedding is a bounded linear map, for either real or complex data. -/
def spatialSlicesCLM (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F]
    (hd : 2 ≤ d) : BUC (ℝ^d) F →L[𝕜] BUC (ℝ^(d - 1)) (BUC ℝ F) :=
  (BUC.curryCLM (𝕜 := 𝕜)).comp
    (BUC.compCLM (𝕜 := 𝕜) (coordinateEquiv hd).symm
      (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous)

@[simp]
theorem spatialSlicesCLM_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F]
    (hd : 2 ≤ d) (v : BUC (ℝ^d) F) : spatialSlicesCLM 𝕜 hd v = spatialSlices hd v := rfl

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- Evaluating a longitudinal BUC value commutes with transverse heat averaging. -/
theorem heatFlowBUC_slice_eval {m : ℕ} (a t : ℝ) (v : BUC (ℝ^m) (BUC ℝ F))
    (y : ℝ^m) (z : ℝ) :
    heatFlowBUC a t v y z = heatFlow a t (fun y' ↦ v y' z) y := by
  let L := BUC.evalCLM (𝕜 := ℝ) (E := F) z
  change L (∫ u, v (y + heatScale a t • u) ∂ProbabilityTheory.stdGaussian (ℝ^m)) = _
  rw [← L.integral_comp_comm
    (integrable_comp_add_heatScale v.continuous ‖v‖ v.norm_apply_le y)]
  rfl

/-- The full scalar diffusion and longitudinal drift factor into independent
transverse heat averaging and longitudinal convective heat evolution. -/
theorem spatialSlices_convectiveHeat (hd : 2 ≤ d) (a t c : ℝ) (v : BUC (ℝ^d) F) :
    spatialSlices hd (convectiveHeatFlowBUC a t (full 0 c) v) =
      heatFlowBUC a t (BUC.postcompCLM (convectiveHeatOperator (E := ℝ) (F := F) a t c)
        (spatialSlices hd v)) := by
  apply BUC.ext
  intro y
  apply BUC.ext
  intro z
  rw [spatialSlices_apply, convectiveHeatFlowBUC_apply, full_add_smul_full hd]
  simp only [smul_zero, add_zero]
  rw [heatFlow_full_coordinates hd a t v v.continuous ‖v‖ v.norm_apply_le,
    heatFlowBUC_slice_eval]
  congr 1
  funext y'
  simp only [BUC.postcompCLM_apply, convectiveHeatOperator_apply,
    convectiveHeatFlowBUC_apply, smul_eq_mul]
  rfl

/-- The scalar principal evolution has the paper's transverse inverse Fourier
representation, as an equality in the longitudinal BUC space. -/
theorem spatial_convectiveHeat_eq_fourierIntegral (hd : 2 ≤ d) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) (c : ℝ) (v : BUC (ℝ^d) ℂ) (y : ℝ^(d - 1)) :
    spatialSlices hd (convectiveHeatFlowBUC a t (full 0 c) v) y =
      ((2 * Real.pi) ^ (d - 1))⁻¹ • ∫ y' : ℝ^(d - 1), ∫ ξ : ℝ^(d - 1),
        Complex.exp (Complex.I * (⟪ξ, y - y'⟫ : ℂ)) •
          (Complex.exp (-((a * t : ℝ) : ℂ) * ‖ξ‖ ^ 2) •
            convectiveHeatFlowBUC a t c (spatialSlices hd v y')) := by
  rw [spatialSlices_convectiveHeat]
  simpa only [finrank_euclideanSpace_fin, BUC.postcompCLM_apply, convectiveHeatOperator_apply] using!
    heatFlowBUC_eq_fourierIntegral ha ht
      (BUC.postcompCLM (convectiveHeatOperator (E := ℝ) (F := ℂ) a t c) (spatialSlices hd v)) y

end

end Planarwave
