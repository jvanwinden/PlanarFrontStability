/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Planarwave.Analysis.FrontCoefficient
import all Planarwave.Analysis.SimpleEigenvaluePerturbation

/-!
# The critical transverse eigenvalue branch

This file specializes the Lyapunov--Schmidt construction to the planar front.  It formalizes the
first part of Proposition 2.1 in the cited paper: for the analytic parameter `q = k²`, the simple
eigenvalue issuing from the translational eigenvalue satisfies

`λ(q) = -d_perp q + O(q²)`,

and hence `λ(k²) = -d_perp k² + O(k⁴)` for real transverse wavenumber `k`.
-/

open Filter Function
open Asymptotics
open scoped Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n)
  (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The critical eigenvalue as a function of the analytic parameter `q = k²`. -/
def frontCriticalEigenvalue (q : ℂ) : ℂ :=
  (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvalueBranch
    (diffusionValue (frontComplexifiedDiffusion D)) q

/-- The corresponding adjoint-normalized eigenvector in the common graph domain. -/
def frontCriticalEigenvector (q : ℂ) : ComplexBUC2 (ℂ^n) :=
  (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvectorBranch
    (diffusionValue (frontComplexifiedDiffusion D)) q

@[simp]
theorem frontCriticalEigenvalue_zero :
    frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ 0 = 0 := by
  simp [frontCriticalEigenvalue]

@[simp]
theorem frontCriticalEigenvector_zero :
    frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ 0 =
      translationModeComplexBUC2 f D c φ ψ h₃ := by
  simp [frontCriticalEigenvector, frontHorizontalSimpleFredholmZeroMode,
    horizontalSimpleFredholmZeroMode]

/-- The paper's adjoint normalization is retained exactly along the branch. -/
theorem frontCriticalEigenvector_normalized (q : ℂ) :
    phaseFunctional ψ h₃.integrable
        (ComplexBUC2.valueCLM (ℂ^n)
          (frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ q)) = 1 := by
  exact (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvectorBranch_normalized
    (diffusionValue (frontComplexifiedDiffusion D)) q

/-- The adjoint-normalized rank-one projection onto the constructed critical eigenline.
It is not yet identified here with the Riesz projection of the perturbed operator. -/
def frontCriticalEigenlineProjection (q : ℂ) :
    BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenlineProjection
    (diffusionValue (frontComplexifiedDiffusion D)) q

@[simp]
theorem frontCriticalEigenlineProjection_zero :
    frontCriticalEigenlineProjection f D c φ ψ h₁ h₂ h₃ 0 =
      profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) := by
  rw [frontCriticalEigenlineProjection,
    (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenlineProjection_zero]
  rfl

/-- The normalized eigenline map is genuinely a projection at every parameter. -/
theorem frontCriticalEigenlineProjection_idempotent (q : ℂ) (w : BUC ℝ (ℂ^n)) :
    frontCriticalEigenlineProjection f D c φ ψ h₁ h₂ h₃ q
        (frontCriticalEigenlineProjection f D c φ ψ h₁ h₂ h₃ q w) =
      frontCriticalEigenlineProjection f D c φ ψ h₁ h₂ h₃ q w := by
  exact (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenlineProjection_idempotent
    (diffusionValue (frontComplexifiedDiffusion D)) q w

/-- In the analytic parameter, the normalized critical-eigenline projection varies by `O(q)`. -/
theorem frontCriticalEigenlineProjection_sub_isBigO :
    (fun q => frontCriticalEigenlineProjection f D c φ ψ h₁ h₂ h₃ q -
        profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃))
      =O[𝓝 0] fun q : ℂ => q := by
  let S := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let B := diffusionValue (frontComplexifiedDiffusion D)
  have hP : S.projection =
      profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) := by
    ext w
    rfl
  change (fun q => S.eigenlineProjection B q -
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃))
      =O[𝓝 0] fun q : ℂ => q
  rw [← hP]
  exact S.eigenlineProjection_sub_projection_isBigO B

/-- Near `q = 0`, the branch solves the concrete common-domain eigenvalue equation. -/
theorem eventually_frontCriticalEigenvalue_equation :
    ∀ᶠ q in 𝓝 0,
      frontLongitudinalPencil f D c φ h₁ h₂ q
          (frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ q) =
        frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q •
          ComplexBUC2.valueCLM (ℂ^n)
            (frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ q) := by
  filter_upwards [
    (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eventually_eigenvalue_equation
      (diffusionValue (frontComplexifiedDiffusion D))] with q hq
  rw [frontLongitudinalPencil_eq_zero_sub]
  rw [frontLongitudinalPencil_zero]
  simpa [frontCriticalEigenvalue, frontCriticalEigenvector,
    frontHorizontalSimpleFredholmZeroMode, horizontalSimpleFredholmZeroMode] using hq

/-- The exact coefficient computed in Proposition 2.1: `λ'(0) = -d_perp`. -/
theorem deriv_frontCriticalEigenvalue_zero :
    deriv (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃) 0 =
      -(d_perp D φ ψ : ℂ) := by
  change deriv
      ((frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvalueBranch
        (diffusionValue (frontComplexifiedDiffusion D))) 0 = _
  rw [(frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).deriv_eigenvalueBranch_zero]
  exact congrArg Neg.neg
    (phaseFunctional_diffusionValue_translationMode f D c φ ψ h₃)

/-- Proposition 2.1 in its natural analytic parameter: `λ(q) = -d_perp q + O(q²)`. -/
theorem frontCriticalEigenvalue_firstOrder_isBigO :
    (fun q => frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q +
        q * (d_perp D φ ψ : ℂ)) =O[𝓝 0] fun q : ℂ => q ^ 2 := by
  simpa only [frontCriticalEigenvalue,
    frontHorizontalSimpleFredholmZeroMode, horizontalSimpleFredholmZeroMode,
    phaseFunctional_diffusionValue_translationMode] using
    (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvalueBranch_firstOrder_isBigO
      (diffusionValue (frontComplexifiedDiffusion D))

/-- The critical eigenvalue as a function of the real transverse wavenumber. -/
def frontCriticalEigenvalueAtWavenumber (k : ℝ) : ℂ :=
  frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ (k ^ 2)

/-- The paper's wavenumber form `λ(k) = -d_perp k² + O(k⁴)`. -/
theorem frontCriticalEigenvalue_wavenumber_isBigO :
    (fun k : ℝ => frontCriticalEigenvalueAtWavenumber f D c φ ψ h₁ h₂ h₃ k +
        (k ^ 2 : ℂ) * (d_perp D φ ψ : ℂ)) =O[𝓝 0]
      fun k : ℝ => ((k : ℂ) ^ 4) := by
  have h := (frontCriticalEigenvalue_firstOrder_isBigO f D c φ ψ h₁ h₂ h₃).comp_tendsto
    (show Tendsto (fun k : ℝ => (k ^ 2 : ℂ)) (𝓝 0) (𝓝 0) by
      have hk : ContinuousAt (fun k : ℝ => (k : ℂ) ^ 2) 0 :=
        (Complex.continuous_ofReal.pow 2).continuousAt
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) ^ 2 by norm_num]
      exact hk)
  refine h.congr' ?_ ?_
  · filter_upwards [] with k
    rfl
  · filter_upwards [] with k
    change (((k : ℂ) ^ 2) ^ 2) = (k : ℂ) ^ 4
    ring

/-- After `q = k²`, the normalized critical-eigenline projection differs from its neutral value
by `O(k²)` in operator norm. -/
theorem frontCriticalEigenlineProjection_wavenumber_isBigO :
    (fun k : ℝ => frontCriticalEigenlineProjection f D c φ ψ h₁ h₂ h₃ (k ^ 2) -
        profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃))
      =O[𝓝 0] fun k : ℝ => ((k : ℂ) ^ 2) := by
  have hk : Tendsto (fun k : ℝ => (k ^ 2 : ℂ)) (𝓝 0) (𝓝 0) := by
    have hk' : ContinuousAt (fun k : ℝ => (k : ℂ) ^ 2) 0 :=
      (Complex.continuous_ofReal.pow 2).continuousAt
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) ^ 2 by norm_num]
    exact hk'
  change ((fun q : ℂ => frontCriticalEigenlineProjection f D c φ ψ h₁ h₂ h₃ q -
      profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)) ∘
      fun k : ℝ => (k ^ 2 : ℂ)) =O[𝓝 0]
        ((fun q : ℂ => q) ∘ fun k : ℝ => (k ^ 2 : ℂ))
  exact (frontCriticalEigenlineProjection_sub_isBigO f D c φ ψ h₁ h₂ h₃).comp_tendsto hk

end

end Planarwave
