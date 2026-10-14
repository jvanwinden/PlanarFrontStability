/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.SpatialDiffusionFourier
import all Planarwave.Analysis.FrontLinearizedMild

/-!
# Spatial Duhamel integrands and reaction slicing

Slicing intertwines the actual spatial reaction multiplication with the
longitudinal reaction multiplication in the Fourier pencil. Joint strong
continuity supplies the continuous Duhamel integrand used in the kernel
representation of the independently constructed spatial evolution.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-- Strong continuity is sufficient for the Duhamel integrand; operator-norm
continuity of the semigroup at time zero is not required. -/
theorem continuous_duhamel_two_semigroups {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (S T : C0Semigroup ℂ E)
    (B : E →L[ℂ] E) (v : E) (t : ℝ) :
    Continuous (fun r : ℝ ↦ S.realOrbit (B (T.realOrbit v r)) (t - r)) :=
  (S.continuous_duhamel_integrand (B.continuous.comp (T.continuous_realOrbit v))).comp
    (continuous_const.prodMk continuous_id)

variable {d m n : ℕ}

local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

/-- The real front coefficient is the same longitudinal multiplication on every slice. -/
theorem spatialSlices_frontReaction (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
    (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
    (hd : 2 ≤ d) (v : BUC (ℝ^d) (ℂ^n)) :
    spatialSlices hd (frontSpatialReactionMultiplication f D c φ h₁ h₂ hd v) =
      BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂) (spatialSlices hd v) := by
  apply BUC.ext
  intro y
  apply BUC.ext
  intro z
  change (complexFrontDerivativeCoefficient f D c φ h₁ h₂) (horizontal (full y z))
      (v (full y z)) = (complexFrontDerivativeCoefficient f D c φ h₁ h₂) z (v (full y z))
  rw [horizontal_full hd]

end

end Planarwave
