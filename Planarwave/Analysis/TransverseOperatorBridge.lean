/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Definitions
import all Planarwave.Analysis.ChallengeBridge
import Planarwave.Analysis.LongitudinalOperator
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The challenge resolvent as a common-domain operator pencil

This file identifies the semantic resolvent predicate in `Challenge.lean` with the Banach-space
operator family used in Section 2 of the paper.  The coefficient is supplied as a bundled BUC
family together with its pointwise identification; a later module constructs that bundle from the
front limits and smoothness assumptions.
-/

open Function Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
  (c : ℝ) (φ : ℝ → ℝ^n)

/-- The continuous complex-linear diffusion matrix associated with the challenge's algebraic
complexification. -/
def complexifiedDiffusion : ℂ^n →L[ℂ] ℂ^n :=
  LinearMap.toContinuousLinearMap (ContinuousLinearMap.complexify D)

@[simp]
theorem complexifiedDiffusion_apply (v : ℂ^n) :
    complexifiedDiffusion D v = (ContinuousLinearMap.complexify D) v :=
  rfl

/-- The common-domain Fourier operator corresponding to the challenge data and a supplied
bundled coefficient family. -/
def challengeTransverseOperator
    (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n)) (k : ℝ) :
    ComplexBUC2 (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  transverseFourierOperator (complexifiedDiffusion D) (c : ℂ) A k

@[simp]
theorem challengeTransverseOperator_apply
    (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n)) (k : ℝ)
    (v : ComplexBUC2 (ℂ^n)) (z : ℝ) :
    challengeTransverseOperator D c A k v z =
      (ContinuousLinearMap.complexify D) (ComplexBUC2.deriv2 (ℂ^n) v z) -
          (k ^ 2 : ℂ) • (ContinuousLinearMap.complexify D) (v z) +
        (c : ℂ) • ComplexBUC2.deriv (ℂ^n) v z + A z (v z) := by
  rfl

/-- The common-domain resolvent map, with the sign convention `L_k - l`. -/
def challengeResolventMap
    (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n)) (k : ℝ) (l : ℂ) :
    ComplexBUC2 (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  challengeTransverseOperator D c A k - l • ComplexBUC2.valueCLM (ℂ^n)

@[simp]
theorem challengeResolventMap_zero
    (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n)) (k : ℝ) :
    challengeResolventMap D c A k 0 = challengeTransverseOperator D c A k := by
  ext v z
  simp [challengeResolventMap]

@[simp]
theorem challengeResolventMap_apply
    (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n)) (k : ℝ) (l : ℂ)
    (v : ComplexBUC2 (ℂ^n)) (z : ℝ) :
    challengeResolventMap D c A k l v z =
      (ContinuousLinearMap.complexify D) (ComplexBUC2.deriv2 (ℂ^n) v z) -
          (k ^ 2 : ℂ) • (ContinuousLinearMap.complexify D) (v z) +
        (c : ℂ) • ComplexBUC2.deriv (ℂ^n) v z + A z (v z) - l • v z := by
  rfl

section PointwiseCoefficient

variable (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n))
variable (hA : ∀ z v, A z v = (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) v)

include hA

/-- A graph-domain solution of the bundled operator equation gives exactly the classical
resolvent solution predicate used by the challenge. -/
theorem isTransverseResolventSolution_of_operatorEquation
    {k : ℝ} {l : ℂ} {v : ComplexBUC2 (ℂ^n)} {w : BUC ℝ (ℂ^n)}
    (hv : challengeResolventMap D c A k l v = w) :
    IsTransverseResolventSolution f D c φ k l (v : ℝ → ℂ^n) (w : ℝ → ℂ^n) := by
  refine ⟨ComplexBUC2.contDiff_two (ℂ^n) v, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · rw [iteratedDeriv_zero]
      change IsBUC (ComplexBUC2.value (ℂ^n) v : ℝ → ℂ^n)
      exact isBUC_coe (ComplexBUC2.value (ℂ^n) v)
    · rw [ComplexBUC2.iteratedDeriv_one_eq]
      change IsBUC (ComplexBUC2.deriv (ℂ^n) v : ℝ → ℂ^n)
      exact isBUC_coe (ComplexBUC2.deriv (ℂ^n) v)
    · rw [ComplexBUC2.iteratedDeriv_two_eq]
      change IsBUC (ComplexBUC2.deriv2 (ℂ^n) v : ℝ → ℂ^n)
      exact isBUC_coe (ComplexBUC2.deriv2 (ℂ^n) v)
  · intro z
    have hz := congrArg (fun g : BUC ℝ (ℂ^n) ↦ g z) hv
    rw [challengeResolventMap_apply] at hz
    rw [hA z (v z)] at hz
    rw [InnerProductSpace.laplacian_eq_iteratedDeriv_real,
      ComplexBUC2.iteratedDeriv_two_eq, ComplexBUC2.deriv_eq]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (k ^ 2) (v z),
      RCLike.real_smul_eq_coe_smul (K := ℂ) c (ComplexBUC2.deriv (ℂ^n) v z)]
    rw [map_sub, LinearMap.map_smul_of_tower]
    have hk_smul :
        ((k ^ 2 : ℝ) : ℂ) • (ContinuousLinearMap.complexify D) (v z) =
          (k : ℂ) ^ 2 • (ContinuousLinearMap.complexify D) (v z) := by
      exact congrArg (fun a : ℂ ↦ a • (ContinuousLinearMap.complexify D) (v z)) (Complex.ofReal_pow k 2)
    calc
      (ContinuousLinearMap.complexify D) (ComplexBUC2.deriv2 (ℂ^n) v z) -
            ((k ^ 2 : ℝ) : ℂ) • (ContinuousLinearMap.complexify D) (v z) +
          (c : ℂ) • ComplexBUC2.deriv (ℂ^n) v z +
            (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) (v z) - l • v z =
          (ContinuousLinearMap.complexify D) (ComplexBUC2.deriv2 (ℂ^n) v z) -
              (k : ℂ) ^ 2 • (ContinuousLinearMap.complexify D) (v z) +
            (c : ℂ) • ComplexBUC2.deriv (ℂ^n) v z +
              (ContinuousLinearMap.complexify (fderiv ℝ f (φ z))) (v z) - l • v z := by rw [hk_smul]
      _ = w z := hz

omit hA

/-- Bundle an unbundled challenge resolvent solution into the common `BUC²` graph domain. -/
def complexBUC2OfTransverseResolventSolution
    {k : ℝ} {l : ℂ} {v w : ℝ → ℂ^n}
    (hv : IsTransverseResolventSolution f D c φ k l v w) :
    ComplexBUC2 (ℂ^n) := by
  let v₀ : BUC ℝ (ℂ^n) := BUC.ofIsBUC (by
    simpa only [iteratedDeriv_zero] using hv.buc 0 (by omega))
  let v₁ : BUC ℝ (ℂ^n) := BUC.ofIsBUC (hv.buc 1 (by omega))
  let v₂ : BUC ℝ (ℂ^n) := BUC.ofIsBUC (hv.buc 2 (by omega))
  refine ⟨((v₀, v₁), v₂), ?_⟩
  intro z
  have hdiff₀ : Differentiable ℝ v := hv.smooth.differentiable (by norm_num)
  have hdiff₁ : Differentiable ℝ (deriv v) := hv.smooth.differentiable_deriv_two
  constructor
  · change HasDerivAt v (iteratedDeriv 1 v z) z
    simpa only [iteratedDeriv_one] using (hdiff₀ z).hasDerivAt
  · change HasDerivAt (iteratedDeriv 1 v) (iteratedDeriv 2 v z) z
    rw [iteratedDeriv_one, show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ,
      iteratedDeriv_one]
    exact (hdiff₁ z).hasDerivAt

@[simp]
theorem complexBUC2OfTransverseResolventSolution_apply
    {k : ℝ} {l : ℂ} {v w : ℝ → ℂ^n}
    (hv : IsTransverseResolventSolution f D c φ k l v w) (z : ℝ) :
    complexBUC2OfTransverseResolventSolution f D c φ hv z = v z :=
  rfl

include hA

/-- A challenge resolvent solution whose underlying function is already represented in the common
graph domain satisfies the bundled operator equation. -/
theorem operatorEquation_of_isTransverseResolventSolution
    {k : ℝ} {l : ℂ} {v : ComplexBUC2 (ℂ^n)} {w : BUC ℝ (ℂ^n)}
    (hv : IsTransverseResolventSolution f D c φ k l
      (v : ℝ → ℂ^n) (w : ℝ → ℂ^n)) :
    challengeResolventMap D c A k l v = w := by
  apply BUC.ext
  intro z
  rw [challengeResolventMap_apply, hA z (v z)]
  have hz := hv.pde z
  rw [InnerProductSpace.laplacian_eq_iteratedDeriv_real,
    ComplexBUC2.iteratedDeriv_two_eq, ComplexBUC2.deriv_eq] at hz
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (k ^ 2) (v z),
    RCLike.real_smul_eq_coe_smul (K := ℂ) c (ComplexBUC2.deriv (ℂ^n) v z)] at hz
  rw [map_sub, LinearMap.map_smul_of_tower] at hz
  have hk_smul :
      ((k ^ 2 : ℝ) : ℂ) • (ContinuousLinearMap.complexify D) (v z) =
        (k : ℂ) ^ 2 • (ContinuousLinearMap.complexify D) (v z) := by
    exact congrArg (fun a : ℂ ↦ a • (ContinuousLinearMap.complexify D) (v z)) (Complex.ofReal_pow k 2)
  rw [← hk_smul]
  exact hz

omit hA

/-- Bundling a classical solution preserves its underlying function. -/
theorem coe_complexBUC2OfTransverseResolventSolution
    {k : ℝ} {l : ℂ} {v w : ℝ → ℂ^n}
    (hv : IsTransverseResolventSolution f D c φ k l v w) :
    (complexBUC2OfTransverseResolventSolution f D c φ hv : ℝ → ℂ^n) = v := by
  funext z
  rfl

include hA

/-- Unique classical resolvent solvability for every BUC forcing is exactly bijectivity of the
common-domain resolvent map.  This is the key bridge from `TransverseSpectrum` to the operator
spectrum used in Section 2 of the paper. -/
theorem challenge_uniqueSolvability_iff_bijective
    (k : ℝ) (l : ℂ) :
    (∀ w : ℝ → ℂ^n, IsBUC w →
        ∃! v : ℝ → ℂ^n, IsTransverseResolventSolution f D c φ k l v w) ↔
      Function.Bijective (challengeResolventMap D c A k l) := by
  rw [Function.bijective_iff_existsUnique]
  constructor
  · intro h w
    obtain ⟨v, hv, hvuniq⟩ := h (w : ℝ → ℂ^n) (isBUC_coe w)
    let V : ComplexBUC2 (ℂ^n) :=
      complexBUC2OfTransverseResolventSolution f D c φ hv
    have hVres : IsTransverseResolventSolution f D c φ k l
        (V : ℝ → ℂ^n) (w : ℝ → ℂ^n) := by
      simpa [V, coe_complexBUC2OfTransverseResolventSolution] using hv
    refine ⟨V, operatorEquation_of_isTransverseResolventSolution f D c φ A hA hVres, ?_⟩
    intro U hU
    apply DFunLike.coe_injective
    funext z
    have hUres := isTransverseResolventSolution_of_operatorEquation f D c φ A hA hU
    have huv : (U : ℝ → ℂ^n) = v := hvuniq (U : ℝ → ℂ^n) hUres
    exact congrFun (huv.trans
      (coe_complexBUC2OfTransverseResolventSolution f D c φ hv).symm) z
  · intro h w hw
    let W : BUC ℝ (ℂ^n) := BUC.ofIsBUC hw
    have hW : (W : ℝ → ℂ^n) = w := by
      funext z
      rfl
    obtain ⟨V, hV, hVuniq⟩ := h W
    have hVres := isTransverseResolventSolution_of_operatorEquation f D c φ A hA hV
    refine ⟨(V : ℝ → ℂ^n), ?_, ?_⟩
    · rw [hW] at hVres
      exact hVres
    · intro v hv
      let U : ComplexBUC2 (ℂ^n) :=
        complexBUC2OfTransverseResolventSolution f D c φ hv
      have hUres : IsTransverseResolventSolution f D c φ k l
          (U : ℝ → ℂ^n) (W : ℝ → ℂ^n) := by
        rw [hW]
        simpa [U, coe_complexBUC2OfTransverseResolventSolution] using hv
      have hU : challengeResolventMap D c A k l U = W :=
        operatorEquation_of_isTransverseResolventSolution f D c φ A hA hUres
      have huv : U = V := hVuniq U hU
      calc
        v = (U : ℝ → ℂ^n) :=
          (coe_complexBUC2OfTransverseResolventSolution f D c φ hv).symm
        _ = (V : ℝ → ℂ^n) := congrArg (fun q : ComplexBUC2 (ℂ^n) ↦ (q : ℝ → ℂ^n)) huv

/-- The semantic transverse spectrum in `Challenge.lean` agrees with failure of bijectivity of
the bundled common-domain resolvent map. -/
theorem mem_transverseSpectrum_iff_not_bijective
    (k : ℝ) (l : ℂ) :
    l ∈ TransverseSpectrum f D c φ k ↔
      ¬ Function.Bijective (challengeResolventMap D c A k l) := by
  change ¬ (∀ w : ℝ → ℂ^n, IsBUC w →
      ∃! v : ℝ → ℂ^n, IsTransverseResolventSolution f D c φ k l v w) ↔ _
  rw [challenge_uniqueSolvability_iff_bijective f D c φ A hA k l]

omit hA

end PointwiseCoefficient

end

end Planarwave
