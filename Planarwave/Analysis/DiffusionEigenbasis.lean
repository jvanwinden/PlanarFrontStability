/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

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
theorem complexDiffusionEigenvectorEquiv_single (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (i : Fin n) :
    complexDiffusionEigenvectorEquiv D hD (EuclideanSpace.single i (1 : ℂ)) =
      embed (hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i) := by
  classical
  ext j
  simp [complexDiffusionEigenvectorEquiv_apply, diffusionEigenvectorMatrix,
    Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, embed, Basis.toMatrix_apply]

end


end Planarwave
