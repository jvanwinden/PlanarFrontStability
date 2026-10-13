/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Coordinates
import Planarwave.Analysis.InverseModulationPDE

/-!
# The challenge Laplacian in split coordinates

The challenge uses the Euclidean norm on full space, whereas the coordinate
product uses the maximum norm. The Laplacian is transported by tracing along
the actual Euclidean coordinate directions, not by treating the product as
an inner-product space.
-/

open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

theorem coordinateEquiv_basis_castSucc {m : ℕ} (hd : 2 ≤ m + 1) (i : Fin m) :
    coordinateEquiv hd (EuclideanSpace.basisFun (Fin (m + 1)) ℝ i.castSucc) =
      (EuclideanSpace.basisFun (Fin m) ℝ i, 0) := by
  apply Prod.ext
  · ext j
    simp [coordinateEquiv, transverse, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      Fin.ext_iff]
  · simp [coordinateEquiv, horizontal, EuclideanSpace.basisFun_apply,
      Fin.ext_iff, ne_of_lt i.isLt]

theorem coordinateEquiv_basis_last {m : ℕ} (hd : 2 ≤ m + 1) :
    coordinateEquiv hd (EuclideanSpace.basisFun (Fin (m + 1)) ℝ (Fin.last m)) =
      ((0 : ℝ^m), 1) := by
  apply Prod.ext
  · ext j
    have hj : (j : ℕ) < m := by simpa only [Nat.add_sub_cancel] using j.isLt
    simp [coordinateEquiv, transverse, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      Fin.ext_iff, ne_of_lt hj]
  · simp [coordinateEquiv, horizontal, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      Fin.ext_iff]

/-- Splitting coordinates preserves the Euclidean Laplacian in the precise
transverse-plus-longitudinal sense used by the modulation calculation. -/
theorem laplacian_eq_splitLaplacian {d : ℕ} (hd : 2 ≤ d)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℝ^d → F) (hu : ContDiff ℝ 2 u) (y : ℝ^(d - 1)) (z : ℝ) :
    Δ u (full y z) = splitLaplacian (fun x ↦ u (full x.1 x.2)) (y, z) := by
  rcases d with _ | m
  · omega
  change ℝ^m at y
  let e : ℝ^(m + 1) ≃L[ℝ] (ℝ^m × ℝ) := coordinateEquiv hd
  let U : ℝ^m × ℝ → F := fun x ↦ u (e.symm x)
  have hU : ContDiff ℝ 2 U := hu.comp e.symm.contDiff
  have hslice : ContDiff ℝ 2 (fun w ↦ U (w, z)) :=
    hU.comp (contDiff_id.prodMk contDiff_const)
  have hline (q : ℝ^(m + 1)) (r : ℝ) :
      u (full (d := m + 1) y z + r • q) = U ((y, z) + r • e q) := by
    dsimp [U]
    rw [map_add, map_smul, e.symm_apply_apply]
    rfl
  have htrans (i : Fin m) :
      deriv (deriv (fun r : ℝ ↦ u (full (d := m + 1) y z + r • EuclideanSpace.basisFun (Fin (m + 1)) ℝ i.castSucc))) 0 =
        deriv (deriv (fun r : ℝ ↦ U (y + r • EuclideanSpace.basisFun (Fin m) ℝ i, z))) 0 := by
    simp only [hline, coordinateEquiv_basis_castSucc hd, Prod.smul_mk, smul_zero,
      Prod.mk_add_mk, add_zero, e]
  have hlong :
      deriv (deriv (fun r : ℝ ↦ u (full (d := m + 1) y z + r • EuclideanSpace.basisFun (Fin (m + 1)) ℝ (Fin.last m)))) 0 =
        deriv (deriv (fun r ↦ U (y, r))) z := by
    simp only [hline, coordinateEquiv_basis_last hd, e]
    rw [secondDeriv_affine_line U hU]
    simpa only [sub_zero] using (secondDeriv_longitudinal_shear U hU y 0 z).symm
  rw [laplacian_eq_sum_secondDeriv (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) u hu,
    Fin.sum_univ_castSucc]
  change _ = splitLaplacian U (y, z)
  simp only [splitLaplacian, htrans, hlong]
  rw [laplacian_eq_sum_secondDeriv (EuclideanSpace.basisFun (Fin m) ℝ) _ hslice]

/-- Positive-time spatial smoothness follows from the challenge's actual
solution predicate; no extra global-in-time smoothness is assumed. -/
theorem IsRDESolution.contDiff_slice {d n : ℕ}
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} {u : ℝ → ℝ^d → ℝ^n}
    (hu : IsRDESolution f D u) {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (u t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have h := hu.smooth.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show (t, x) ∈ Set.Ioi 0 ×ˢ Set.univ from ⟨ht, Set.mem_univ x⟩))
  exact h.comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- The physical reaction--diffusion equation in the coordinates required by
`frontInverseModulatedPerturbation_pde`, directly from `IsRDESolution`. -/
theorem IsRDESolution.split_pde {d n : ℕ} (hd : 2 ≤ d)
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} {u : ℝ → ℝ^d → ℝ^n}
    (hu : IsRDESolution f D u) {t : ℝ} (ht : 0 < t) (y : ℝ^(d - 1)) (z : ℝ) :
    deriv (fun r ↦ u r (full y z)) t =
      D (splitLaplacian (fun x ↦ u t (full x.1 x.2)) (y, z)) + f (u t (full y z)) := by
  rw [hu.pde t ht, laplacian_eq_splitLaplacian hd _
    ((IsRDESolution.contDiff_slice hu ht).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))]

end

end Planarwave
