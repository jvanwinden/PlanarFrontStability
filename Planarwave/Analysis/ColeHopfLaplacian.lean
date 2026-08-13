/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/

module

public import Planarwave.Analysis.ColeHopf
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

public section

/-!
# The Laplacian of the Cole--Hopf transform

This file proves the spatial chain rule used in Section 5 of the cited paper.  If `σ` is twice
continuously differentiable, then

`Δ (coleHopf β ∘ σ) = exp (β σ) * (Δ σ + β * ‖∇σ‖²)`.

The proof follows the paper's coordinate calculation: restrict to each line through the point,
apply the one-dimensional second-derivative chain rule, and sum over an orthonormal basis.
-/

open Function
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

namespace Planarwave

section Lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear map parametrizing the line in direction `v`. -/
@[expose]
noncomputable def lineCLM (v : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

@[simp]
theorem lineCLM_apply (v : E) (t : ℝ) : lineCLM v t = t • v := by
  rfl

end Lines

section DirectionalDerivatives

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first derivative along the affine line `x + ℝv` is the Fréchet derivative applied to
`v`. -/
lemma deriv_line (σ : E → ℝ) (hσ : ContDiff ℝ 2 σ) (x v : E) :
    deriv (fun t : ℝ => σ (x + t • v)) 0 = fderiv ℝ σ x v := by
  rw [← iteratedDeriv_one, iteratedDeriv_eq_iteratedFDeriv]
  have hshift : ContDiff ℝ 2 (fun z : E => σ (x + z)) := by
    fun_prop
  rw [show (fun t : ℝ => σ (x + t • v)) =
      (fun z : E => σ (x + z)) ∘ lineCLM v by rfl]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right
      (lineCLM v) hshift 0 (by norm_num)]
  rw [iteratedFDeriv_comp_add_left 1 x]
  simp [lineCLM]

/-- The second derivative along the affine line `x + ℝv` is the second Fréchet derivative with
both arguments equal to `v`. -/
lemma iteratedDeriv_line_two (σ : E → ℝ) (hσ : ContDiff ℝ 2 σ) (x v : E) :
    iteratedDeriv 2 (fun t : ℝ => σ (x + t • v)) 0 =
      iteratedFDeriv ℝ 2 σ x ![v, v] := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hshift : ContDiff ℝ 2 (fun z : E => σ (x + z)) := by
    fun_prop
  rw [show (fun t : ℝ => σ (x + t • v)) =
      (fun z : E => σ (x + z)) ∘ lineCLM v by rfl]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right
      (lineCLM v) hshift 0 le_rfl]
  rw [iteratedFDeriv_comp_add_left 2 x]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    lineCLM_apply, one_smul, zero_smul, add_zero]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The second directional derivative chain rule for the Cole--Hopf transform. -/
lemma iteratedFDeriv_two_coleHopf_comp (β : ℝ) (σ : E → ℝ)
    (hσ : ContDiff ℝ 2 σ) (x v : E) :
    iteratedFDeriv ℝ 2 (coleHopf β ∘ σ) x ![v, v] =
      Real.exp (β * σ x) *
        (iteratedFDeriv ℝ 2 σ x ![v, v] + β * (fderiv ℝ σ x v) ^ 2) := by
  have h2top : (2 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hg : ContDiffAt ℝ 2 (coleHopf β) (σ x) :=
    (contDiff_coleHopf β).contDiffAt.of_le h2top
  have hf : ContDiffAt ℝ 2 (fun t : ℝ => σ (x + t • v)) 0 := by
    fun_prop
  have hcomp : ContDiff ℝ 2 (coleHopf β ∘ σ) :=
    ((contDiff_coleHopf β).of_le h2top).comp hσ
  rw [← iteratedDeriv_line_two (coleHopf β ∘ σ) hcomp x v]
  change iteratedDeriv 2
      (coleHopf β ∘ fun t : ℝ => σ (x + t • v)) 0 = _
  rw [iteratedDeriv_comp_two (by simpa using hg) hf]
  rw [deriv_line σ hσ x v, iteratedDeriv_line_two σ hσ x v,
    deriv_coleHopf]
  simp only [zero_smul, add_zero]
  have htwo : iteratedDeriv 2 (coleHopf β) (σ x) =
      β * Real.exp (β * σ x) := by
    simpa [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one] using second_deriv_coleHopf β (σ x)
  rw [htwo]
  ring

end DirectionalDerivatives

section Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Pointwise spatial Cole--Hopf chain rule.  This is the identity used to transform the viscous
Hamilton--Jacobi equation in Section 5 of the cited paper. -/
theorem laplacian_coleHopf_comp_apply (β : ℝ) (σ : E → ℝ)
    (hσ : ContDiff ℝ 2 σ) (x : E) :
    Δ (coleHopf β ∘ σ) x =
      Real.exp (β * σ x) * (Δ σ x + β * ‖∇ σ x‖ ^ 2) := by
  let b := stdOrthonormalBasis ℝ E
  have hgrad : ∑ i, (fderiv ℝ σ x (b i)) ^ 2 = ‖∇ σ x‖ ^ 2 := by
    simpa only [inner_gradient_left] using b.sum_sq_inner_left (∇ σ x)
  rw [congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (coleHopf β ∘ σ) b) x,
    congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis σ b) x]
  simp_rw [iteratedFDeriv_two_coleHopf_comp β σ hσ x]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hgrad]

/-- Spatial Cole--Hopf chain rule as an equality of scalar fields. -/
theorem laplacian_coleHopf_comp (β : ℝ) (σ : E → ℝ) (hσ : ContDiff ℝ 2 σ) :
    Δ (coleHopf β ∘ σ) =
      fun x => Real.exp (β * σ x) * (Δ σ x + β * ‖∇ σ x‖ ^ 2) := by
  funext x
  exact laplacian_coleHopf_comp_apply β σ hσ x

end Laplacian

end Planarwave
