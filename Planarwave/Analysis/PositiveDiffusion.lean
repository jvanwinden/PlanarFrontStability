/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Coercivity of a positive diffusion operator

This file records the finite-dimensional coercivity step used in Lemma 2.2 of the cited paper.
The proof takes the minimum of the quadratic form on the compact unit sphere.  Positivity and
injectivity make the quadratic form strictly positive there, and homogeneity gives the estimate
on the whole space.
-/

open scoped InnerProductSpace NNReal
open Metric Set

noncomputable section

namespace Planarwave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a positive injective real operator, its quadratic form is strictly positive away from
zero.  This fact does not require finite dimensionality. -/
theorem ContinuousLinearMap.IsPositive.inner_map_self_pos_of_injective
    {D : E →L[ℝ] E} (hD : D.IsPositive) (hDinj : Function.Injective D)
    {x : E} (hx : x ≠ 0) : 0 < ⟪D x, x⟫_ℝ := by
  let B : LinearMap.BilinForm ℝ E := (innerₗ E).comp D.toLinearMap
  have hB_nonneg : ∀ y, 0 ≤ B y y := by
    intro y
    exact hD.inner_nonneg_left y
  have hB_symm : LinearMap.IsSymm B := by
    constructor
    intro y z
    change ⟪D y, z⟫_ℝ = ⟪D z, y⟫_ℝ
    rw [hD.inner_left_eq_inner_right, real_inner_comm]
  have hzero : ⟪D x, x⟫_ℝ = 0 → D x = 0 := by
    intro hxx
    have hxker : B x = 0 :=
      (B.apply_apply_same_eq_zero_iff hB_nonneg hB_symm).mp hxx
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    simpa [B] using LinearMap.congr_fun hxker (D x)
  apply lt_of_le_of_ne (hD.inner_nonneg_left x)
  intro h
  apply hx
  apply hDinj
  simpa using hzero h.symm

/-- **Finite-dimensional coercivity for positive diffusion.**

On a nontrivial finite-dimensional real inner product space, a positive injective continuous
linear endomorphism has a strictly positive lower quadratic-form bound.  This is the coercivity
bridge used in Lemma 2.2 of the paper. -/
theorem exists_pos_mul_sq_norm_le_inner_of_positive_injective
    [FiniteDimensional ℝ E] [Nontrivial E]
    (D : E →L[ℝ] E) (hD : D.IsPositive) (hDinj : Function.Injective D) :
    ∃ μ > 0, ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪D x, x⟫_ℝ := by
  let q : E → ℝ := fun x ↦ ⟪D x, x⟫_ℝ
  have hq_cont : Continuous q := by
    dsimp [q]
    fun_prop
  have hq_sphere_pos : ∀ x ∈ sphere (0 : E) 1, 0 < q x := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by simpa using hx
    have hxne : x ≠ 0 := by
      intro hxzero
      subst x
      norm_num at hxnorm
    exact ContinuousLinearMap.IsPositive.inner_map_self_pos_of_injective hD hDinj hxne
  obtain ⟨μ, hμ, hμ_sphere⟩ :=
    (isCompact_sphere (0 : E) 1).exists_forall_le' hq_cont.continuousOn hq_sphere_pos
  refine ⟨μ, hμ, fun x ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : (‖x‖⁻¹ : ℝ) • x ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm hx
  have hscaled := hμ_sphere ((‖x‖⁻¹ : ℝ) • x) hunit
  have hscale :
      q ((‖x‖⁻¹ : ℝ) • x) = ‖x‖⁻¹ ^ 2 * q x := by
    simp only [q, D.map_smul, real_inner_smul_left, inner_smul_right]
    ring
  rw [hscale] at hscaled
  calc
    μ * ‖x‖ ^ 2 ≤ (‖x‖⁻¹ ^ 2 * q x) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hscaled (sq_nonneg ‖x‖)
    _ = q x := by field_simp [ne_of_gt hxnorm]

/-- In particular, a positive injective finite-dimensional diffusion operator is invertible in
the ring of continuous linear endomorphisms. -/
theorem isUnit_of_positive_injective
    [FiniteDimensional ℝ E] [Nontrivial E]
    (D : E →L[ℝ] E) (hD : D.IsPositive) (hDinj : Function.Injective D) : IsUnit D := by
  obtain ⟨μ, hμ, hcoercive⟩ :=
    exists_pos_mul_sq_norm_le_inner_of_positive_injective D hD hDinj
  let c : ℝ≥0 := ⟨μ, hμ.le⟩
  have hc : 0 < c := by exact_mod_cast hμ
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map D hc
  intro x
  change ‖x‖ ^ 2 * μ ≤ ‖⟪D x, x⟫_ℝ‖
  simpa [mul_comm, Real.norm_eq_abs, abs_of_nonneg (hD.inner_nonneg_left x)] using hcoercive x

/-- Hence the underlying function of the diffusion operator is bijective. -/
theorem bijective_of_positive_injective
    [FiniteDimensional ℝ E] [Nontrivial E]
    (D : E →L[ℝ] E) (hD : D.IsPositive) (hDinj : Function.Injective D) :
    Function.Bijective D := by
  exact ContinuousLinearMap.isUnit_iff_bijective.mp
    (isUnit_of_positive_injective D hD hDinj)

end Planarwave
