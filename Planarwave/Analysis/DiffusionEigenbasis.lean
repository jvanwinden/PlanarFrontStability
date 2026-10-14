/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Definitions
import all Planarwave.Analysis.FrontCoefficient
public import Planarwave.Analysis.BUCEquiv
public import Planarwave.Analysis.DiagonalDiffusionSemigroup
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# The complexified diffusion eigenbasis

This file constructs the matrix `J` from the proof of Lemma 2.2.  Starting from the real
orthonormal eigenbasis of the symmetric positive diffusion matrix, its entries are embedded in
`ℂ`; the resulting matrix is unitary and hence gives a continuous complex-linear equivalence.
-/

open WithLp
open scoped Matrix

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ}

/-- The real matrix whose columns are the orthonormal diffusion eigenvectors. -/
def diffusionEigenvectorMatrix (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) :
    Matrix (Fin n) (Fin n) ℝ :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix
    (hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin).toBasis

/-- The same eigenvector matrix over `ℂ`, bundled as a unitary matrix. -/
def complexDiffusionEigenvectorUnitary
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) : Matrix.unitaryGroup (Fin n) ℂ := by
  classical
  let b := hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let U : Matrix (Fin n) (Fin n) ℝ := diffusionEigenvectorMatrix D hD
  have hU : Uᴴ * U = 1 := by
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  refine ⟨U.map Complex.ofReal, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  calc
    (U.map Complex.ofReal)ᴴ * U.map Complex.ofReal =
        Uᴴ.map Complex.ofReal * U.map Complex.ofReal := by
          rw [Matrix.conjTranspose_map Complex.ofReal (fun x ↦ by simp)]
    _ = (Uᴴ * U).map Complex.ofReal :=
      (Matrix.map_mul (f := Complex.ofRealHom)).symm
    _ = 1 := by rw [hU]; simp

/-- The complex-linear eigenvector change of coordinates `J` on the challenge's Euclidean state
space.  It maps eigenvector coordinates to the original coordinates. -/
def complexDiffusionEigenvectorEquiv
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) : ℂ^n ≃L[ℂ] ℂ^n :=
  (((WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
      (Matrix.UnitaryGroup.toLinearEquiv (complexDiffusionEigenvectorUnitary D hD))).trans
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm).toContinuousLinearEquiv

/-- The finite-dimensional eigenvector equivalence is multiplication by the complexified real
eigenvector matrix. -/
theorem complexDiffusionEigenvectorEquiv_apply (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (v : ℂ^n) :
    complexDiffusionEigenvectorEquiv D hD v =
      Matrix.toEuclideanLin ((diffusionEigenvectorMatrix D hD).map Complex.ofReal) v := by
  rfl

/-- The `i`-th standard coordinate vector is sent to the embedded real diffusion eigenvector. -/
@[simp]
private theorem complexDiffusionEigenvectorEquiv_single (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (i : Fin n) :
    complexDiffusionEigenvectorEquiv D hD (EuclideanSpace.single i (1 : ℂ)) =
      embed (hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i) := by
  classical
  ext j
  simp [complexDiffusionEigenvectorEquiv_apply, diffusionEigenvectorMatrix,
    Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, embed, Module.Basis.toMatrix_apply,
    Pi.single_apply]

/-- Eigenvector coordinates with the finite product norm on the coordinate space. -/
def diffusionCoordinatesEquiv (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) :
    (Fin n → ℂ) ≃L[ℂ] ℂ^n :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.trans (complexDiffusionEigenvectorEquiv D hD)

@[simp]
private theorem diffusionCoordinatesEquiv_single (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (i : Fin n) :
    diffusionCoordinatesEquiv D hD (Pi.single i (1 : ℂ)) =
      embed (hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i) :=
  complexDiffusionEigenvectorEquiv_single D hD i

/-- The real diffusion eigenvectors remain eigenvectors of the complexified operator. -/
private theorem complexifiedDiffusion_eigenvector (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (i : Fin n) :
    frontComplexifiedDiffusion D (diffusionCoordinatesEquiv D hD (Pi.single i (1 : ℂ))) =
      (diffusionEigenvalues D hD i : ℂ) •
        diffusionCoordinatesEquiv D hD (Pi.single i (1 : ℂ)) := by
  rw [diffusionCoordinatesEquiv_single]
  change challengeComplexifyCLM D (embed _) = _
  rw [challengeComplexifyCLM_embed]
  have heig := hD.toLinearMap.isSymmetric.apply_eigenvectorBasis finrank_euclideanSpace_fin i
  change D _ = diffusionEigenvalues D hD i • _ at heig
  rw [heig]
  ext j
  simp [embed]

/-- The concrete eigenbasis diagonalizes the challenge's complexified diffusion matrix. -/
private theorem complexifiedDiffusion_coordinates (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (v : Fin n → ℂ) :
    frontComplexifiedDiffusion D (diffusionCoordinatesEquiv D hD v) =
      diffusionCoordinatesEquiv D hD (fun i => (diffusionEigenvalues D hD i : ℂ) * v i) := by
  classical
  let J := diffusionCoordinatesEquiv D hD
  have hv : v = ∑ i, v i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  calc
    frontComplexifiedDiffusion D (J v) =
        ∑ i, v i • frontComplexifiedDiffusion D (J (Pi.single i (1 : ℂ))) := by
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul]
    _ = ∑ i, v i • ((diffusionEigenvalues D hD i : ℂ) • J (Pi.single i (1 : ℂ))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [complexifiedDiffusion_eigenvector]
    _ = J (fun i => (diffusionEigenvalues D hD i : ℂ) * v i) := by
      simp only [← map_smul, ← map_sum]
      congr 1
      ext j
      simp [Pi.single_apply, mul_comm]

/-- The actual change of coordinates between the diagonal product of scalar BUC spaces and the
challenge's complex vector-valued BUC space. -/
def diffusionBUCCoordinatesEquiv (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) :
    (Fin n → BUC ℝ ℂ) ≃L[ℂ] BUC ℝ (ℂ^n) :=
  (BUC.piCLE (α := ℝ) (𝕜 := ℂ) (X := fun _ : Fin n => ℂ)).symm.trans
    (BUC.postcompCLE (diffusionCoordinatesEquiv D hD))

@[simp]
theorem diffusionBUCCoordinatesEquiv_apply (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (v : Fin n → BUC ℝ ℂ) (z : ℝ) :
    diffusionBUCCoordinatesEquiv D hD v z = diffusionCoordinatesEquiv D hD (fun i => v i z) := rfl

@[simp]
theorem diffusionBUCCoordinatesEquiv_symm_apply (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (v : BUC ℝ (ℂ^n)) (i : Fin n) (z : ℝ) :
    (diffusionBUCCoordinatesEquiv D hD).symm v i z =
      (diffusionCoordinatesEquiv D hD).symm (v z) i := rfl

end


end Planarwave
