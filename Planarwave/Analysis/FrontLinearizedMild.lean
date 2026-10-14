/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionGenerator
import all Planarwave.Analysis.DiffusionSemigroup
import all Planarwave.Analysis.FrontCoefficient
import Planarwave.Analysis.SemigroupVolterraSeries

/-!
# Mild trajectories of the real-frequency linearized front operator

This specializes the Volterra construction to the first bounded perturbation in Lemma 2.2:
`L̂_ξ = D ∂zz + c ∂z - |ξ|² D + f'(φ)`. The coefficient multiplication is bounded independently
of frequency. Its common-domain sum with the principal generator is exactly the longitudinal
pencil already used in the spectral analysis. The finite-time trajectory operator is constructed
from the convergent Volterra series and satisfies the corresponding Duhamel equation.

`FrontLinearizedSemigroup` identifies these paths with a C₀ semigroup, proves its full
generator-domain equality, and establishes the frequency-uniform exponential growth estimate.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)

/-- Multiplication by the complexified reaction derivative along the front. -/
def frontReactionMultiplication : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  BUC.operatorApplyCLM (complexFrontDerivativeCoefficient f D c φ h₁ h₂)

/-- The exact bounded-perturbation identity on the common `BUC²` domain. -/
theorem frontLongitudinalPencil_eq_principal_add (q : ℝ) :
    frontLongitudinalPencil f D c φ h₁ h₂ (q : ℂ) =
      longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 +
        (frontReactionMultiplication f D c φ h₁ h₂).comp (ComplexBUC2.valueCLM (ℂ^n)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply BUC.ext
  intro z
  simp [frontLongitudinalPencil, longitudinalOperator_apply, frontReactionMultiplication]

variable [Nontrivial (ℝ^n)]

/-- The real-frequency linearized mild trajectory as a bounded linear function of initial data. -/
def frontLinearizedMildPathOperator (q : ℝ) (T : NNReal) :
    BUC ℝ (ℂ^n) →L[ℂ] C0Semigroup.TimePath (E := BUC ℝ (ℂ^n)) T :=
  (frontDiffusionC0Semigroup D h₁.positive c q).perturbedPathOperator
    (frontReactionMultiplication f D c φ h₁ h₂) T

/-- The constructed path starts at the prescribed longitudinal BUC datum. -/
@[simp]
theorem frontLinearizedMildPathOperator_zero (q : ℝ) (T : NNReal) (v₀ : BUC ℝ (ℂ^n)) :
    frontLinearizedMildPathOperator f D c φ h₁ h₂ q T v₀ ⟨0, le_rfl, T.2⟩ = v₀ := by
  exact C0Semigroup.perturbedPathOperator_zero _ _ _ _

end

end Planarwave
