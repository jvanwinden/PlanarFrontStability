/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSemigroup
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

/-!
# Heat flow and the Laplacian under orthogonal changes of coordinates
-/

open Function MeasureTheory ProbabilityTheory
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

variable {E G F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Gaussian heat averaging is invariant under a linear isometric change of coordinates. -/
theorem heatFlow_comp_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] G) (a t : ℝ)
    (f : G → F) (hf : Continuous f) :
    heatFlow a t (f ∘ e) = heatFlow a t f ∘ e := by
  funext x
  rw [comp_apply, heatFlow, heatFlow, ← stdGaussian_map e,
    integral_map e.continuous.measurable.aemeasurable
      (f := fun z : G => f (e x + heatScale a t • z))
      ((hf.comp (by fun_prop)).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with z
  simp [map_add, map_smul]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G] [CompleteSpace F] in
/-- The Laplacian is invariant under orthogonal coordinate changes. -/
theorem laplacian_comp_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] G) (f : G → F)
    (hf : ContDiff ℝ 2 f) : Δ (f ∘ e) = Δ f ∘ e := by
  let b := stdOrthonormalBasis ℝ E
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (b.map e)]
  funext x
  dsimp only [comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x le_rfl
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  fin_cases j <;> simp

end

end Planarwave
