/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSpatialGenerator
import Planarwave.Analysis.SemigroupPerturbationIntertwining

/-!
# Transverse translation symmetry of the spatial front semigroup

The principal matrix heat flow commutes with every translation. The front
coefficient commutes with transverse translations, so bounded perturbation
preserves this symmetry. This establishes the actual spatial translation
invariance behind the transverse Fourier representation.
-/

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

section Principal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Heat flow with a fixed drift still commutes with all spatial translations. -/
theorem convectiveHeatFlowBUC_translate (a t : ℝ) (b s : E) (v : BUC E F) :
    convectiveHeatFlowBUC a t b (BUC.translate s v) = BUC.translate s (convectiveHeatFlowBUC a t b v) := by
  rw [convectiveHeatFlowBUC, heatFlowBUC_translate, BUC.translate_add,
    convectiveHeatFlowBUC, BUC.translate_add, add_comm]

variable {n : ℕ} [Nontrivial (ℝ^n)]

/-- The full matrix diffusion semigroup commutes with spatial translation. -/
theorem spatialDiffusionC0Semigroup_translate (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (b s : E) (t : NNReal) (v : BUC E (ℂ^n)) :
    spatialDiffusionC0Semigroup D hD b t (BUC.translate s v) =
      BUC.translate s (spatialDiffusionC0Semigroup D hD b t v) := by
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  have hi (i : Fin n) : J.symm (BUC.translate s v) i = BUC.translate s (J.symm v i) := by
    ext x
    rfl
  rw [spatialDiffusionC0Semigroup_apply, spatialDiffusionC0Semigroup_apply]
  apply BUC.ext
  intro x
  change diffusionCoordinatesEquiv D hD
      (fun i ↦ convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t b (J.symm (BUC.translate s v) i) x) =
    diffusionCoordinatesEquiv D hD
      (fun i ↦ convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t b (J.symm v i) (x - s))
  congr 1
  funext i
  rw [hi, convectiveHeatFlowBUC_translate]
  rfl

end Principal

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (hd : 2 ≤ d)

/-- The reaction coefficient is constant in every transverse direction. -/
theorem frontSpatialReactionMultiplication_translate (s : ℝ^d) (hs : horizontal s = 0)
    (v : BUC (ℝ^d) (ℂ^n)) :
    frontSpatialReactionMultiplication f D c φ h₁ h₂ hd (BUC.translate s v) =
      BUC.translate s (frontSpatialReactionMultiplication f D c φ h₁ h₂ hd v) := by
  ext x
  have hz : horizontal (x - s) = horizontal x := by
    change horizontalCLM hd (x - s) = horizontalCLM hd x
    rw [map_sub, horizontalCLM_apply hd s, hs, sub_zero]
  simp only [frontSpatialReactionMultiplication_apply, BUC.translate_apply, hz]

variable [Nontrivial (ℝ^n)]

/-- Transverse translations intertwine the full perturbed spatial evolution. -/
theorem frontSpatialC0Semigroup_translate (s : ℝ^d) (hs : horizontal s = 0)
    (t : NNReal) (v : BUC (ℝ^d) (ℂ^n)) :
    frontSpatialC0Semigroup f D c φ h₁ h₂ hd t (BUC.translate s v) =
      BUC.translate s (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) := by
  let S := spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)
  let B := frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
  let U : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n) := BUC.translateCLM s
  have hU (r : NNReal) : (S r).comp U = U.comp (S r) := by
    apply ContinuousLinearMap.ext
    intro w
    exact spatialDiffusionC0Semigroup_translate D h₁.positive (frontSpatialDrift hd c) s r w
  have hB : B.comp U = U.comp B := by
    apply ContinuousLinearMap.ext
    intro w
    exact frontSpatialReactionMultiplication_translate f D c φ h₁ h₂ hd s hs w
  exact congrArg (fun L : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n) ↦ L v)
    (S.boundedPerturbation_comm B U hU hB t)

/-- In the challenge's split coordinates, every transverse displacement is admissible. -/
theorem frontSpatialC0Semigroup_transverse_translate (y : ℝ^(d - 1))
    (t : NNReal) (v : BUC (ℝ^d) (ℂ^n)) :
    frontSpatialC0Semigroup f D c φ h₁ h₂ hd t (BUC.translate (full y 0) v) =
      BUC.translate (full y 0) (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) :=
  frontSpatialC0Semigroup_translate f D c φ h₁ h₂ hd (full y 0) (horizontal_full hd y 0) t v

end

end Planarwave
