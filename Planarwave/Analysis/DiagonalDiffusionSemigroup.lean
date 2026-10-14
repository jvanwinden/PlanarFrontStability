/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Planarwave.Analysis.ConvectiveHeatSemigroup
public import Planarwave.Analysis.PositiveDiffusion
public import Planarwave.Analysis.SemigroupOperations

@[expose] public section

/-!
# Diagonal diffusion semigroups

This file formalizes the diagonal heat-semigroup calculation in the proof of Lemma 2.2.  Each
coordinate evolves by a scalar convective heat semigroup with diffusion rate `a i`, together with
the Fourier damping factor `exp (-q (a i) t)`.  A uniform lower bound `μ ≤ a i` gives the exact
decay estimate `exp (-μ q t)`.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

section DiagonalDiffusion

variable {ι : Type*} [Fintype ι]

/-- The coordinatewise semigroup generated formally by
`diag(a i) ∂zz + c ∂z - q diag(a i)` on the diagonalized state space. -/
def diagonalDiffusionC0Semigroup (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (c q : ℝ) : C0Semigroup ℂ (∀ _ : ι, BUC ℝ ℂ) :=
  C0Semigroup.pi (X := fun _ : ι ↦ BUC ℝ ℂ) fun i ↦
    (complexConvectiveHeatC0Semigroup (a i) (ha i) c).rescaleRealExp (-q * a i)

@[simp]
theorem diagonalDiffusionC0Semigroup_apply
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (c q : ℝ)
    (t : NNReal) (v : ∀ _ : ι, BUC ℝ ℂ) (i : ι) :
    diagonalDiffusionC0Semigroup a ha c q t v i =
      (Real.exp ((-q * a i) * (t : ℝ)) : ℂ) •
        convectiveHeatFlowBUC (a i) t c (v i) := rfl

/-- The `i`-th coordinate semigroup has the expected Fourier damping bound. -/
theorem norm_diagonalDiffusionC0Semigroup_coordinate_le
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (c q : ℝ) (t : NNReal) (i : ι) :
    ‖(complexConvectiveHeatC0Semigroup (a i) (ha i) c).rescaleRealExp
        (-q * a i) t‖ ≤
      Real.exp ((-q * a i) * (t : ℝ)) := by
  apply C0Semigroup.norm_rescaleRealExp_of_isContraction_le
  intro s
  exact norm_complexConvectiveHeatOperator_le (a i) s c

/-- Uniform diagonal diffusion estimate used before conjugating back by the eigenvector matrix
in the paper. -/
theorem norm_diagonalDiffusionC0Semigroup_le
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (c q μ : ℝ)
    (hμ : ∀ i, μ ≤ a i) (hq : 0 ≤ q) (t : NNReal) :
    ‖diagonalDiffusionC0Semigroup a ha c q t‖ ≤
      Real.exp (-μ * q * (t : ℝ)) := by
  apply C0Semigroup.norm_pi_le _ _ (Real.exp_pos _).le
  intro i
  calc
    ‖(complexConvectiveHeatC0Semigroup (a i) (ha i) c).rescaleRealExp
        (-q * a i) t‖ ≤
        Real.exp ((-q * a i) * (t : ℝ)) :=
      norm_diagonalDiffusionC0Semigroup_coordinate_le a ha c q t i
    _ ≤ Real.exp (-μ * q * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hqa : q * μ ≤ q * a i := mul_le_mul_of_nonneg_left (hμ i) hq
      have hneg : -(q * a i) ≤ -(q * μ) := neg_le_neg hqa
      have ht := mul_le_mul_of_nonneg_right hneg t.2
      simpa [mul_assoc, mul_comm, mul_left_comm] using ht

end DiagonalDiffusion

section ConjugatedDiagonalDiffusion

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The diagonal diffusion semigroup transported back to a vector-valued `BUC` space by a
continuous change of coordinates.  In the paper this equivalence is induced by the eigenvector
matrix `J`. -/
def conjugatedDiagonalDiffusionC0Semigroup
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (c q : ℝ)
    (J : (∀ _ : ι, BUC ℝ ℂ) ≃L[ℂ] BUC ℝ V) : C0Semigroup ℂ (BUC ℝ V) :=
  (diagonalDiffusionC0Semigroup a ha c q).conjugate J

@[simp]
theorem conjugatedDiagonalDiffusionC0Semigroup_apply
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (c q : ℝ)
    (J : (∀ _ : ι, BUC ℝ ℂ) ≃L[ℂ] BUC ℝ V)
    (t : NNReal) (v : BUC ℝ V) :
    conjugatedDiagonalDiffusionC0Semigroup a ha c q J t v =
      J (diagonalDiffusionC0Semigroup a ha c q t (J.symm v)) := rfl

/-- Conjugating the diagonal estimate produces exactly the fixed condition-number prefactor
appearing before the bounded perturbation argument in Lemma 2.2. -/
theorem norm_conjugatedDiagonalDiffusionC0Semigroup_le
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (c q μ : ℝ)
    (hμ : ∀ i, μ ≤ a i) (hq : 0 ≤ q)
    (J : (∀ _ : ι, BUC ℝ ℂ) ≃L[ℂ] BUC ℝ V) (t : NNReal) :
    ‖conjugatedDiagonalDiffusionC0Semigroup a ha c q J t‖ ≤
      (‖J.toContinuousLinearMap‖ * ‖J.symm.toContinuousLinearMap‖) *
        Real.exp (-μ * q * (t : ℝ)) := by
  exact (diagonalDiffusionC0Semigroup a ha c q).norm_conjugate_le_of_norm_le J t
    (norm_diagonalDiffusionC0Semigroup_le a ha c q μ hμ hq t)

end ConjugatedDiagonalDiffusion

section PositiveDiffusionRates

variable {n : ℕ} [Nontrivial (ℝ^n)]

/-- Eigenvalues of the symmetric positive diffusion operator in the orthonormal eigenbasis used
in the paper. -/
def diffusionEigenvalues (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) : Fin n → ℝ :=
  hD.toLinearMap.isSymmetric.eigenvalues finrank_euclideanSpace_fin

/-- The diffusion eigenvalues admit a common strictly positive lower bound. -/
theorem exists_pos_le_diffusionEigenvalues
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) :
    ∃ μ > 0, ∀ i, μ ≤ diffusionEigenvalues D hD i := by
  obtain ⟨μ, hμ, hcoercive⟩ :=
    exists_pos_mul_sq_norm_le_inner_of_positive_injective D hD hDinj
  refine ⟨μ, hμ, fun i ↦ ?_⟩
  have hi := hcoercive
    (hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i)
  have heig := hD.toLinearMap.isSymmetric.apply_eigenvectorBasis
    finrank_euclideanSpace_fin i
  change D (hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i) =
    diffusionEigenvalues D hD i •
      hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i at heig
  rw [heig] at hi
  simpa [real_inner_smul_left] using hi

/-- In particular, every diffusion eigenvalue is nonnegative. -/
theorem diffusionEigenvalues_nonneg
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (i : Fin n) :
    0 ≤ diffusionEigenvalues D hD i := by
  exact hD.toLinearMap.nonneg_eigenvalues finrank_euclideanSpace_fin i

end PositiveDiffusionRates

end

end Planarwave
