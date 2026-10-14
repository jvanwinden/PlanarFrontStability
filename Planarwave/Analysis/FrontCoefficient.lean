/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Statement
import Planarwave.Analysis.TwoEndedBUC
import Planarwave.Analysis.LongitudinalOperator
import all Planarwave.Analysis.TransverseOperatorBridge
import all Planarwave.Analysis.PhaseFunctional
import all Planarwave.Analysis.TranslationMode
import all Planarwave.Analysis.ConcreteFredholm

/-!
# The linearized reaction coefficient along a traveling front

Section 2 of de Rijk--van Winden studies the common-domain family

`L(k) = D ∂_z^2 + c ∂_z + f'(φ(z)) - k^2 D`.

This file constructs the coefficient `z ↦ f'(φ(z))` as a bundled bounded uniformly continuous
family, including the real-to-complex matrix conversion used in `Challenge.lean`, and then
specializes the abstract longitudinal operator to the challenge data.
-/

open Filter Function Set Topology
open MeasureTheory
open scoped ContDiff InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ}

/-- The challenge's algebraic complexification, bundled as a continuous complex-linear map. -/
def challengeComplexifyCLM (L : ℝ^n →L[ℝ] ℝ^n) : ℂ^n →L[ℂ] ℂ^n :=
  LinearMap.toContinuousLinearMap (ContinuousLinearMap.complexify L)

@[simp]
theorem challengeComplexifyCLM_apply (L : ℝ^n →L[ℝ] ℝ^n) (v : ℂ^n) :
    challengeComplexifyCLM L v = (ContinuousLinearMap.complexify L) v :=
  rfl

/-- Complexification agrees with the original real map on the canonical real subspace. -/
@[simp]
theorem challengeComplexifyCLM_embed (L : ℝ^n →L[ℝ] ℝ^n) (x : ℝ^n) :
    challengeComplexifyCLM L (embed x) = embed (L x) := by
  ext i
  have hmatrix :
      Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm L.toLinearMap) x = L x :=
    DFunLike.congr_fun
      (LinearEquiv.apply_symm_apply Matrix.toEuclideanLin L.toLinearMap) x
  have hi := congrArg (fun y : ℝ^n => y.ofLp i) hmatrix
  change ∑ j, Matrix.toEuclideanLin.symm L.toLinearMap i j * x.ofLp j =
    (L x).ofLp i at hi
  change ∑ j,
      (((Matrix.toEuclideanLin (𝕜 := ℝ)).symm L.toLinearMap i j : ℝ) : ℂ) *
        (x.ofLp j : ℂ) = ((L x).ofLp i : ℂ)
  exact_mod_cast hi

/-- Complexification is real-linear as a map between the finite-dimensional operator spaces. -/
def challengeComplexifyLinearMap :
    (ℝ^n →L[ℝ] ℝ^n) →ₗ[ℝ] (ℂ^n →L[ℂ] ℂ^n) where
  toFun := challengeComplexifyCLM
  map_add' L M := by
    ext v i
    simp [challengeComplexifyCLM, ContinuousLinearMap.complexify, Matrix.mulVec,
      dotProduct, add_mul, Finset.sum_add_distrib]
  map_smul' r L := by
    ext v i
    simp [challengeComplexifyCLM, ContinuousLinearMap.complexify, Matrix.mulVec,
      dotProduct, mul_assoc, Finset.mul_sum]

/-- Continuous-linear packaging of real-to-complex matrix extension. -/
def challengeComplexifyOperator :
    (ℝ^n →L[ℝ] ℝ^n) →L[ℝ] (ℂ^n →L[ℂ] ℂ^n) :=
  challengeComplexifyLinearMap.toContinuousLinearMap

@[simp]
theorem challengeComplexifyOperator_apply (L : ℝ^n →L[ℝ] ℝ^n) :
    challengeComplexifyOperator L = challengeComplexifyCLM L :=
  rfl

section AlongFront

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ : ℝ → ℝ^n)

/-- The left end state selected from `IsSmoothFront.endpoints`. -/
def frontLeftState (h₂ : IsSmoothFront f D c φ) : ℝ^n :=
  h₂.endpoints.choose

/-- The right end state selected from `IsSmoothFront.endpoints`. -/
def frontRightState (h₂ : IsSmoothFront f D c φ) : ℝ^n :=
  h₂.endpoints.choose_spec.choose

theorem tendsto_frontLeftState (h₂ : IsSmoothFront f D c φ) :
    Tendsto φ atBot (𝓝 (frontLeftState f D c φ h₂)) :=
  h₂.endpoints.choose_spec.choose_spec.1

theorem tendsto_frontRightState (h₂ : IsSmoothFront f D c φ) :
    Tendsto φ atTop (𝓝 (frontRightState f D c φ h₂)) :=
  h₂.endpoints.choose_spec.choose_spec.2

/-- The real Fréchet derivative `f'(φ(z))`, bundled as a BUC family. -/
def realFrontDerivativeCoefficient
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) :
    BUC ℝ (ℝ^n →L[ℝ] ℝ^n) :=
  BUC.fderivAlongTwoEnded h₂.smooth.continuous
    (tendsto_frontLeftState f D c φ h₂) (tendsto_frontRightState f D c φ h₂)
    h₁.smooth (by simp)

@[simp]
theorem realFrontDerivativeCoefficient_apply
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (z : ℝ) :
    realFrontDerivativeCoefficient f D c φ h₁ h₂ z = fderiv ℝ f (φ z) :=
  by simp [realFrontDerivativeCoefficient]

/-- The Section 2 coefficient `z ↦ (f'(φ(z)))_ℂ`, as a BUC family of complex-linear maps. -/
def complexFrontDerivativeCoefficient
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) :
    BUC ℝ (ℂ^n →L[ℂ] ℂ^n) :=
  BUC.postcompCLM challengeComplexifyOperator
    (realFrontDerivativeCoefficient f D c φ h₁ h₂)

@[simp]
theorem complexFrontDerivativeCoefficient_apply
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (z : ℝ) (v : ℂ^n) :
    complexFrontDerivativeCoefficient f D c φ h₁ h₂ z v =
      (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) v :=
  by simp [complexFrontDerivativeCoefficient]

/-- The diffusion matrix on the complexified state space. -/
def frontComplexifiedDiffusion : ℂ^n →L[ℂ] ℂ^n :=
  challengeComplexifyCLM D

@[simp]
theorem frontComplexifiedDiffusion_apply (v : ℂ^n) :
    frontComplexifiedDiffusion D v = (ContinuousLinearMap.complexify D) v :=
  rfl

/-- The analytic common-domain pencil `L(q)` from Section 2, specialized to the challenge data. -/
def frontLongitudinalPencil
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (q : ℂ) :
    ComplexBUC2 (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) q
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂)

@[simp]
theorem frontLongitudinalPencil_apply
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (q : ℂ)
    (v : ComplexBUC2 (ℂ^n)) (z : ℝ) :
    frontLongitudinalPencil f D c φ h₁ h₂ q v z =
      (ContinuousLinearMap.complexify D) (ComplexBUC2.deriv2 (ℂ^n) v z) - q • (ContinuousLinearMap.complexify D) (v z) +
        (c : ℂ) • ComplexBUC2.deriv (ℂ^n) v z +
          (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) (v z) :=
  by simp [frontLongitudinalPencil]

/-- The transverse real-wavenumber member `L(k²)` of the common-domain pencil. -/
def frontTransverseOperator
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (k : ℝ) :
    ComplexBUC2 (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  frontLongitudinalPencil f D c φ h₁ h₂ (k ^ 2)

@[simp]
theorem frontTransverseOperator_apply
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (k : ℝ)
    (v : ComplexBUC2 (ℂ^n)) (z : ℝ) :
    frontTransverseOperator f D c φ h₁ h₂ k v z =
      (ContinuousLinearMap.complexify D) (ComplexBUC2.deriv2 (ℂ^n) v z) -
          (k ^ 2 : ℂ) • (ContinuousLinearMap.complexify D) (v z) +
        (c : ℂ) • ComplexBUC2.deriv (ℂ^n) v z +
          (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) (v z) :=
  by simp [frontTransverseOperator]

/-- Exact affine dependence of the concrete pencil on `q`. -/
theorem frontLongitudinalPencil_eq_zero_sub
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (q : ℂ) :
    frontLongitudinalPencil f D c φ h₁ h₂ q =
      frontLongitudinalPencil f D c φ h₁ h₂ 0 -
        q • diffusionValue (frontComplexifiedDiffusion D) := by
  exact longitudinalOperator_eq_zero_sub (frontComplexifiedDiffusion D) (c : ℂ) q
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂)

/-- At `q = 0` the analytic pencil is the horizontal challenge operator. -/
@[simp]
theorem frontLongitudinalPencil_zero
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) :
    frontLongitudinalPencil f D c φ h₁ h₂ 0 =
      challengeTransverseOperator D c
        (complexFrontDerivativeCoefficient f D c φ h₁ h₂) 0 := by
  ext v z
  simp

/-- The concrete common-domain resolvent pencil `L(k)-l`. -/
def frontChallengeResolventMap
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
    (k : ℝ) (l : ℂ) :
    ComplexBUC2 (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  challengeResolventMap D c (complexFrontDerivativeCoefficient f D c φ h₁ h₂) k l

@[simp]
theorem frontChallengeResolventMap_apply
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
    (k : ℝ) (l : ℂ) (v : ComplexBUC2 (ℂ^n)) (z : ℝ) :
    frontChallengeResolventMap f D c φ h₁ h₂ k l v z =
      (ContinuousLinearMap.complexify D) (ComplexBUC2.deriv2 (ℂ^n) v z) -
          (k ^ 2 : ℂ) • (ContinuousLinearMap.complexify D) (v z) +
        (c : ℂ) • ComplexBUC2.deriv (ℂ^n) v z +
          (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) (v z) - l • v z := by
  exact challengeResolventMap_apply D c
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂) k l v z

/-- The semantic challenge spectrum is exactly the failure of bijectivity of the concrete
common-domain resolvent. -/
theorem mem_transverseSpectrum_iff_frontChallengeResolventMap_not_bijective
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
    (k : ℝ) (l : ℂ) :
    l ∈ TransverseSpectrum f D c φ k ↔
      ¬ Function.Bijective (frontChallengeResolventMap f D c φ h₁ h₂ k l) := by
  exact mem_transverseSpectrum_iff_not_bijective f D c φ
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂)
    (fun z v => complexFrontDerivativeCoefficient_apply f D c φ h₁ h₂ z v) k l

end AlongFront

section ConcreteSpectralData

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n)

/-- The phase coefficient of the diffusion perturbation on the translation mode is precisely
the paper's transverse diffusion coefficient `d_perp`.  This is the numerator entering the
first derivative of the critical eigenvalue. -/
theorem phaseFunctional_diffusionValue_translationMode
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    phaseFunctional ψ h₃.integrable
        (diffusionValue (frontComplexifiedDiffusion D)
          (translationModeComplexBUC2 f D c φ ψ h₃)) =
      (d_perp D φ ψ : ℂ) := by
  let w : BUC ℝ (ℂ^n) :=
    diffusionValue (frontComplexifiedDiffusion D)
      (translationModeComplexBUC2 f D c φ ψ h₃)
  change phaseFunctional ψ h₃.integrable w = (d_perp D φ ψ : ℂ)
  rw [phaseFunctional_apply]
  calc
    (∫ z, ⟪embed (ψ z), w z⟫_ℂ) =
        ∫ z, (⟪ψ z, D (deriv φ z)⟫_ℝ : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp [w]
      change ⟪embed (ψ z), challengeComplexifyCLM D (embed (deriv φ z))⟫_ℂ = _
      rw [challengeComplexifyCLM_embed, inner_embed]
    _ = ((∫ z, ⟪ψ z, D (deriv φ z)⟫_ℝ : ℝ) : ℂ) := integral_ofReal
    _ = (d_perp D φ ψ : ℂ) := rfl

variable (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The abstract Fredholm zero-mode package instantiated solely from the three challenge
hypotheses; no auxiliary coefficient assumption remains. -/
def frontHorizontalSimpleFredholmZeroMode :
    SimpleFredholmZeroMode (BUC ℝ (ℂ^n)) (ComplexBUC2 (ℂ^n)) :=
  horizontalSimpleFredholmZeroMode f D c φ ψ h₃
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂)
    (fun z v => complexFrontDerivativeCoefficient_apply f D c φ h₁ h₂ z v)

/-- The concrete horizontal operator restricted to its phase-zero domain and codomain
complements. -/
def frontHorizontalComplementEquiv :=
  horizontalComplementEquiv f D c φ ψ h₃
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂)
    (fun z v => complexFrontDerivativeCoefficient_apply f D c φ h₁ h₂ z v)


end ConcreteSpectralData

end

end Planarwave
