/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Planarwave.Analysis.FredholmProjection
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-!
# Perturbation of a simple Fredholm eigenvalue

This is the abstract Lyapunov--Schmidt argument used in Proposition 2.1 of the planar-wave
paper.  Starting from a simple Fredholm zero mode of `A₀ : Dom → X` and a bounded common-domain
perturbation `B : Dom → X`, we apply the Banach-space implicit function theorem to

`(A₀ - q B)(φ + u) - λ i(φ + u) = 0`,  `ℓ(i u) = 0`.

The complementary inverse constructed in `FredholmProjection` makes the partial derivative in
`(λ, u)` invertible.  Consequently this file constructs a smooth, normalized eigenpair branch,
proves its eigenvalue equation near zero, and computes the coefficient

`λ'(0) = -ℓ(B φ)`.
-/

open Function Filter
open scoped Topology ContDiff
open Asymptotics

universe u v

noncomputable section

namespace Planarwave
namespace SimpleFredholmZeroMode

variable {X : Type u} {Dom : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

variable (S : SimpleFredholmZeroMode X Dom)

noncomputable instance domainComplementCompleteSpace : CompleteSpace S.domainComplement :=
  (S.functional.comp S.inclusion).isClosed_ker.completeSpace_coe

noncomputable instance ambientComplementCompleteSpace : CompleteSpace S.ambientComplement :=
  S.functional.isClosed_ker.completeSpace_coe

/-! ## The invertible partial linearization -/

/-- Projection onto the Fredholm complement, with its codomain restricted to `ker ℓ`. -/
def complementProjection : X →L[ℂ] S.ambientComplement :=
  (ContinuousLinearMap.id ℂ X - S.projection).codRestrict S.ambientComplement fun w => by
    change S.functional (w - S.projection w) = 0
    exact S.complement_mem_kernel_functional w

@[simp]
theorem complementProjection_coe (w : X) :
    (S.complementProjection w : X) = w - S.projection w :=
  rfl

@[simp]
theorem complementProjection_inclusion_mode :
    S.complementProjection (S.inclusion S.mode) = 0 := by
  apply Subtype.ext
  change S.inclusion S.mode -
    S.functional (S.inclusion S.mode) • S.inclusion S.mode = 0
  rw [S.normalized, one_smul, sub_self]

@[simp]
theorem complementProjection_ambientComplement (w : S.ambientComplement) :
    S.complementProjection (w : X) = w := by
  apply Subtype.ext
  change (w : X) - S.functional (w : X) • S.inclusion S.mode = (w : X)
  have hw : S.functional (w : X) = 0 := w.property
  rw [hw, zero_smul, sub_zero]

/-- The partial derivative of the eigenvalue equation in `(λ,u)` at the unperturbed eigenpair. -/
def eigenpairLinearization : (ℂ × S.domainComplement) →L[ℂ] X :=
  (S.ambientComplement.subtypeL.comp
      (S.complementOperator.comp
        (ContinuousLinearMap.snd ℂ ℂ S.domainComplement))) -
    (ContinuousLinearMap.fst ℂ ℂ S.domainComplement).smulRight (S.inclusion S.mode)

@[simp]
theorem eigenpairLinearization_apply (p : ℂ × S.domainComplement) :
    S.eigenpairLinearization p =
      S.operator (p.2 : Dom) - p.1 • S.inclusion S.mode :=
  rfl

/-- Explicit inverse of the partial eigenpair linearization. -/
def eigenpairLinearizationInverse : X →L[ℂ] (ℂ × S.domainComplement) :=
  (-S.functional).prod
    (S.complementInverse.comp S.complementProjection)

@[simp]
theorem eigenpairLinearizationInverse_apply (w : X) :
    S.eigenpairLinearizationInverse w =
      (-S.functional w, S.complementInverse (S.complementProjection w)) :=
  rfl

theorem eigenpairLinearization_leftInverse :
    LeftInverse S.eigenpairLinearizationInverse S.eigenpairLinearization := by
  rintro ⟨a, u⟩
  apply Prod.ext
  · simp [eigenpairLinearization, S.functional_operator, S.normalized]
  · rw [eigenpairLinearizationInverse_apply]
    simp only [eigenpairLinearization_apply]
    have hproj : S.complementProjection
        (S.operator (u : Dom) - a • S.inclusion S.mode) = S.complementOperator u := by
      apply Subtype.ext
      simp [S.functional_operator, S.normalized]
    rw [hproj, S.complementInverse_complementOperator]

theorem eigenpairLinearization_rightInverse :
    RightInverse S.eigenpairLinearizationInverse S.eigenpairLinearization := by
  intro w
  rw [eigenpairLinearizationInverse_apply, eigenpairLinearization_apply]
  have hop : S.operator
      (S.complementInverse (S.complementProjection w) : Dom) =
      (S.complementProjection w : X) := by
    simpa only [← S.complementOperator_apply] using
      congrArg Subtype.val (S.complementOperator_complementInverse (S.complementProjection w))
  rw [hop, complementProjection_coe]
  simp [projection_apply]

/-- The partial eigenpair linearization is a Banach-space isomorphism. -/
def eigenpairLinearizationEquiv : (ℂ × S.domainComplement) ≃L[ℂ] X :=
  ContinuousLinearEquiv.equivOfInverse' S.eigenpairLinearization
    S.eigenpairLinearizationInverse
    (ContinuousLinearMap.ext fun w => S.eigenpairLinearization_rightInverse w)
    (ContinuousLinearMap.ext fun p => S.eigenpairLinearization_leftInverse p)

@[simp]
theorem eigenpairLinearizationEquiv_apply (p : ℂ × S.domainComplement) :
    S.eigenpairLinearizationEquiv p = S.eigenpairLinearization p :=
  rfl

theorem eigenpairLinearization_isInvertible :
    S.eigenpairLinearization.IsInvertible := by
  exact ⟨S.eigenpairLinearizationEquiv, rfl⟩

/-! ## The implicit eigenpair branch -/

/-- The `q` coordinate on the variables of the implicit eigenpair equation. -/
def eigenpairParameterCoordinate :
    (ℂ × (ℂ × S.domainComplement)) →L[ℂ] ℂ :=
  ContinuousLinearMap.fst ℂ ℂ (ℂ × S.domainComplement)

/-- The `λ` coordinate on the variables of the implicit eigenpair equation. -/
def eigenpairEigenvalueCoordinate :
    (ℂ × (ℂ × S.domainComplement)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ S.domainComplement).comp
    (ContinuousLinearMap.snd ℂ ℂ (ℂ × S.domainComplement))

/-- The graph-domain correction coordinate, including the subtype embedding. -/
def eigenpairCorrectionCoordinate :
    (ℂ × (ℂ × S.domainComplement)) →L[ℂ] Dom :=
  S.domainComplement.subtypeL.comp
    ((ContinuousLinearMap.snd ℂ ℂ S.domainComplement).comp
      (ContinuousLinearMap.snd ℂ ℂ (ℂ × S.domainComplement)))

@[simp] theorem eigenpairParameterCoordinate_apply
    (p : ℂ × (ℂ × S.domainComplement)) : S.eigenpairParameterCoordinate p = p.1 := rfl

@[simp] theorem eigenpairEigenvalueCoordinate_apply
    (p : ℂ × (ℂ × S.domainComplement)) : S.eigenpairEigenvalueCoordinate p = p.2.1 := rfl

@[simp] theorem eigenpairCorrectionCoordinate_apply
    (p : ℂ × (ℂ × S.domainComplement)) : S.eigenpairCorrectionCoordinate p = (p.2.2 : Dom) := rfl

/-- The normalized eigenvalue equation in the variables `q` and `(λ,u)`, where `u ∈ ker (ℓ ∘ i)`.
The affine family is `A(q) = A₀ - q B`. -/
def eigenpairEquation (B : Dom →L[ℂ] X) (p : ℂ × (ℂ × S.domainComplement)) : X :=
  S.operator (S.mode + S.eigenpairCorrectionCoordinate p) -
    S.eigenpairParameterCoordinate p •
      B (S.mode + S.eigenpairCorrectionCoordinate p) -
      S.eigenpairEigenvalueCoordinate p •
        S.inclusion (S.mode + S.eigenpairCorrectionCoordinate p)

@[simp]
theorem eigenpairEquation_zero (B : Dom →L[ℂ] X) :
    S.eigenpairEquation B (0, (0, 0)) = 0 := by
  simp [eigenpairEquation]

/-- Total derivative of the eigenpair equation at the unperturbed eigenpair. -/
def eigenpairEquationDerivative (B : Dom →L[ℂ] X) :
    (ℂ × (ℂ × S.domainComplement)) →L[ℂ] X :=
  S.operator.comp S.eigenpairCorrectionCoordinate -
    S.eigenpairParameterCoordinate.smulRight (B S.mode) -
      S.eigenpairEigenvalueCoordinate.smulRight (S.inclusion S.mode)

@[simp]
theorem eigenpairEquationDerivative_apply (B : Dom →L[ℂ] X)
    (p : ℂ × (ℂ × S.domainComplement)) :
    S.eigenpairEquationDerivative B p =
      S.operator (p.2.2 : Dom) - p.1 • B S.mode - p.2.1 • S.inclusion S.mode :=
  rfl

theorem hasFDerivAt_eigenpairEquation (B : Dom →L[ℂ] X) :
    HasFDerivAt (S.eigenpairEquation B) (S.eigenpairEquationDerivative B) (0, (0, 0)) := by
  let p₀ : ℂ × (ℂ × S.domainComplement) := (0, (0, 0))
  have hu : HasFDerivAt
      (fun p : ℂ × (ℂ × S.domainComplement) =>
        S.mode + S.eigenpairCorrectionCoordinate p)
      S.eigenpairCorrectionCoordinate p₀ :=
    S.eigenpairCorrectionCoordinate.hasFDerivAt.const_add S.mode
  have hA := S.operator.hasFDerivAt.comp p₀ hu
  have hB := B.hasFDerivAt.comp p₀ hu
  have hq : HasFDerivAt (S.eigenpairParameterCoordinate :
      (ℂ × (ℂ × S.domainComplement)) → ℂ) S.eigenpairParameterCoordinate p₀ :=
    S.eigenpairParameterCoordinate.hasFDerivAt
  have hlambda : HasFDerivAt (S.eigenpairEigenvalueCoordinate :
      (ℂ × (ℂ × S.domainComplement)) → ℂ) S.eigenpairEigenvalueCoordinate p₀ :=
    S.eigenpairEigenvalueCoordinate.hasFDerivAt
  have hi := S.inclusion.hasFDerivAt.comp p₀ hu
  have h := (hA.sub (hq.smul hB)).sub (hlambda.smul hi)
  convert h using 1 <;> try rfl <;> try exact Subsingleton.elim _ _
  apply ContinuousLinearMap.ext
  intro p
  simp [eigenpairEquationDerivative, p₀]

theorem contDiff_eigenpairEquation (B : Dom →L[ℂ] X) :
    ContDiff ℂ ω (S.eigenpairEquation B) := by
  have hu : ContDiff ℂ ω
      (fun p : ℂ × (ℂ × S.domainComplement) =>
        S.mode + S.eigenpairCorrectionCoordinate p) :=
    contDiff_const.add S.eigenpairCorrectionCoordinate.contDiff
  have hA := S.operator.contDiff.comp hu
  have hB := B.contDiff.comp hu
  have hq : ContDiff ℂ ω (S.eigenpairParameterCoordinate :
      (ℂ × (ℂ × S.domainComplement)) → ℂ) :=
    S.eigenpairParameterCoordinate.contDiff
  have hlambda : ContDiff ℂ ω (S.eigenpairEigenvalueCoordinate :
      (ℂ × (ℂ × S.domainComplement)) → ℂ) :=
    S.eigenpairEigenvalueCoordinate.contDiff
  have hi := S.inclusion.contDiff.comp hu
  convert (hA.sub (hq.smul hB)).sub (hlambda.smul hi) using 1
  ext p
  rfl

theorem fderiv_eigenpairEquation (B : Dom →L[ℂ] X) :
    fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) = S.eigenpairEquationDerivative B :=
  (S.hasFDerivAt_eigenpairEquation B).fderiv

theorem eigenpairEquation_partialDerivative (B : Dom →L[ℂ] X) :
    fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) ∘L
        ContinuousLinearMap.inr ℂ ℂ (ℂ × S.domainComplement) =
      S.eigenpairLinearization := by
  rw [S.fderiv_eigenpairEquation B]
  apply ContinuousLinearMap.ext
  intro p
  simp [eigenpairEquationDerivative]

theorem eigenpairEquation_partialDerivative_isInvertible (B : Dom →L[ℂ] X) :
    (fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) ∘L
      ContinuousLinearMap.inr ℂ ℂ (ℂ × S.domainComplement)).IsInvertible := by
  rw [S.eigenpairEquation_partialDerivative B]
  exact S.eigenpairLinearization_isInvertible

/-- The smooth local branch `(λ(q), u(q))` selected by the normalization `ℓ(iu)=0`. -/
noncomputable def eigenpairBranch (B : Dom →L[ℂ] X) : ℂ → ℂ × S.domainComplement :=
  (S.contDiff_eigenpairEquation B).contDiffAt.implicitFunction (by simp)
    (S.eigenpairEquation_partialDerivative_isInvertible B)

/-- The critical eigenvalue branch. -/
noncomputable def eigenvalueBranch (B : Dom →L[ℂ] X) (q : ℂ) : ℂ :=
  (S.eigenpairBranch B q).1

/-- The normalized critical eigenvector branch in the common graph domain. -/
noncomputable def eigenvectorBranch (B : Dom →L[ℂ] X) (q : ℂ) : Dom :=
  S.mode + (S.eigenpairBranch B q).2

@[simp]
theorem eigenpairBranch_zero (B : Dom →L[ℂ] X) :
    S.eigenpairBranch B 0 = (0, 0) := by
  exact (S.contDiff_eigenpairEquation B).contDiffAt.implicitFunction_apply_self
    (by simp) (S.eigenpairEquation_partialDerivative_isInvertible B)

@[simp]
theorem eigenvalueBranch_zero (B : Dom →L[ℂ] X) : S.eigenvalueBranch B 0 = 0 := by
  simp [eigenvalueBranch]

@[simp]
theorem eigenvectorBranch_zero (B : Dom →L[ℂ] X) : S.eigenvectorBranch B 0 = S.mode := by
  simp [eigenvectorBranch]

/-- Near zero the constructed branch solves the affine eigenvalue equation. -/
theorem eventually_eigenpairEquation_branch (B : Dom →L[ℂ] X) :
    ∀ᶠ q in 𝓝 0, S.eigenpairEquation B (q, S.eigenpairBranch B q) = 0 := by
  simpa [eigenpairBranch] using
    (S.contDiff_eigenpairEquation B).contDiffAt.eventually_apply_implicitFunction
      (by simp) (S.eigenpairEquation_partialDerivative_isInvertible B)

theorem eventually_eigenvalue_equation (B : Dom →L[ℂ] X) :
    ∀ᶠ q in 𝓝 0,
      S.operator (S.eigenvectorBranch B q) - q • B (S.eigenvectorBranch B q) =
        S.eigenvalueBranch B q • S.inclusion (S.eigenvectorBranch B q) := by
  filter_upwards [S.eventually_eigenpairEquation_branch B] with q hq
  simpa [eigenpairEquation, eigenvectorBranch, eigenvalueBranch, sub_eq_zero] using hq

/-- The branch retains the paper's adjoint normalization exactly. -/
theorem eigenvectorBranch_normalized (B : Dom →L[ℂ] X) (q : ℂ) :
    S.functional (S.inclusion (S.eigenvectorBranch B q)) = 1 := by
  have hu : S.functional (S.inclusion ((S.eigenpairBranch B q).2 : Dom)) = 0 :=
    (S.eigenpairBranch B q).2.property
  simp [eigenvectorBranch, S.normalized, hu]

/-- Applying the cokernel functional to the eigenvalue equation gives the scalar
Lyapunov--Schmidt equation used in the paper. -/
theorem eventually_eigenvalue_equation_scalar (B : Dom →L[ℂ] X) :
    ∀ᶠ q in 𝓝 0,
      S.eigenvalueBranch B q =
        -q * S.functional (B (S.eigenvectorBranch B q)) := by
  filter_upwards [S.eventually_eigenvalue_equation B] with q hq
  have h := congrArg S.functional hq
  simpa [S.functional_operator, S.eigenvectorBranch_normalized] using h.symm

/-! ## First-order coefficient -/

/-- First derivative of the full `(λ,u)` branch furnished by the implicit function theorem. -/
theorem hasStrictFDerivAt_eigenpairBranch (B : Dom →L[ℂ] X) :
    HasStrictFDerivAt (S.eigenpairBranch B)
      (-(fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) ∘L
          ContinuousLinearMap.inr ℂ ℂ (ℂ × S.domainComplement)).inverse ∘L
        (fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) ∘L
          ContinuousLinearMap.inl ℂ ℂ (ℂ × S.domainComplement))) 0 := by
  exact (S.contDiff_eigenpairEquation B).contDiffAt.hasStrictFDerivAt_implicitFunction
    (by simp) (S.eigenpairEquation_partialDerivative_isInvertible B)

/-- The first derivative of the critical eigenvalue is the phase pairing of the
perturbation with the normalized zero mode, with the sign dictated by
`A(q) = A₀ - qB`. -/
theorem hasDerivAt_eigenvalueBranch (B : Dom →L[ℂ] X) :
    HasDerivAt (S.eigenvalueBranch B) (-S.functional (B S.mode)) 0 := by
  have hinv :
      (fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) ∘L
          ContinuousLinearMap.inr ℂ ℂ (ℂ × S.domainComplement)).inverse =
        S.eigenpairLinearizationInverse := by
    rw [S.eigenpairEquation_partialDerivative B]
    apply ContinuousLinearMap.inverse_eq
    · apply ContinuousLinearMap.ext
      intro w
      exact S.eigenpairLinearization_rightInverse w
    · apply ContinuousLinearMap.ext
      intro p
      exact S.eigenpairLinearization_leftInverse p
  have h := (S.hasStrictFDerivAt_eigenpairBranch B).hasFDerivAt
  have hfst := hasFDerivAt_fst.comp 0 h
  have hcoeff :
      (ContinuousLinearMap.fst ℂ ℂ S.domainComplement ∘L
          (-(fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) ∘L
              ContinuousLinearMap.inr ℂ ℂ (ℂ × S.domainComplement)).inverse ∘L
            (fderiv ℂ (S.eigenpairEquation B) (0, (0, 0)) ∘L
              ContinuousLinearMap.inl ℂ ℂ (ℂ × S.domainComplement)))) 1 =
        -S.functional (B S.mode) := by
    rw [hinv, S.fderiv_eigenpairEquation]
    simp [eigenpairEquationDerivative, eigenpairLinearizationInverse]
  have hderiv := hfst.hasDerivAt
  rw [hcoeff] at hderiv
  change HasDerivAt (Prod.fst ∘ S.eigenpairBranch B)
    (-S.functional (B S.mode)) 0
  exact hderiv

/-- The normalized eigenvector correction has the first-order bound `O(q)` in the graph
domain. -/
theorem eigenvectorBranch_sub_mode_isBigO (B : Dom →L[ℂ] X) :
    (fun q => S.eigenvectorBranch B q - S.mode) =O[𝓝 0]
      fun q : ℂ => q := by
  have hbranch :=
    (S.hasStrictFDerivAt_eigenpairBranch B).hasFDerivAt.isBigO_sub
  let C : (ℂ × S.domainComplement) →L[ℂ] Dom :=
    S.domainComplement.subtypeL.comp
      (ContinuousLinearMap.snd ℂ ℂ S.domainComplement)
  have hC := C.isBigO_comp
    (fun q : ℂ => S.eigenpairBranch B q - S.eigenpairBranch B 0) (𝓝 0)
  have hcorr := hC.trans hbranch
  simpa [C, eigenvectorBranch] using hcorr

/-- The first-order eigenvalue expansion with its rigorous quadratic remainder:
`λ(q) = -q ℓ(Bφ) + O(q²)`. -/
theorem eigenvalueBranch_firstOrder_isBigO (B : Dom →L[ℂ] X) :
    (fun q => S.eigenvalueBranch B q + q * S.functional (B S.mode))
      =O[𝓝 0] fun q : ℂ => q ^ 2 := by
  let F : Dom →L[ℂ] ℂ := S.functional.comp B
  have hphase :
      (fun q => F (S.eigenvectorBranch B q - S.mode)) =O[𝓝 0]
        fun q : ℂ => q :=
    (F.isBigO_comp (fun q => S.eigenvectorBranch B q - S.mode) (𝓝 0)).trans
      (S.eigenvectorBranch_sub_mode_isBigO B)
  have hprod := (isBigO_refl (fun q : ℂ => q) (𝓝 0)).mul hphase
  apply hprod.neg_left.congr'
  · filter_upwards [S.eventually_eigenvalue_equation_scalar B] with q hq
    rw [hq]
    simp [F, map_sub]
    ring
  · filter_upwards [] with q
    simp [pow_two]

end SimpleFredholmZeroMode
end Planarwave
