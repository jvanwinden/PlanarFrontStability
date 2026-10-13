/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.TemporalCutoff
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# BUC approximations of the scaling variation

The derivative of `φ(z/α)` at `α = 1` contains the linear factor `z`.
To pair its differential equation with an integrable adjoint, approximate
that factor by smooth compactly supported functions. Their first derivatives
converge to one and their second derivatives to zero, with uniform bounds.
-/

open Filter
open scoped Topology ContDiff

namespace Planarwave

noncomputable section

/-- A compactly supported smooth two-jet agreeing with the identity near zero. -/
theorem exists_linear_cutoff_jet : ∃ η η₁ η₂ : BUC ℝ ℝ,
    (∀ z, HasDerivAt η (η₁ z) z) ∧ (∀ z, HasDerivAt η₁ (η₂ z) z) ∧ η₁ 0 = 1 := by
  let ρ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let u : ℝ → ℝ := fun z ↦ z * ρ z
  have hu : ContDiff ℝ ∞ u := contDiff_id.mul ρ.contDiff
  have hc : HasCompactSupport u := ρ.hasCompactSupport.mul_left
  have hu₁ := (contDiff_infty_iff_deriv.mp hu).2
  have hu₂ := (contDiff_infty_iff_deriv.mp hu₁).2
  refine ⟨BUC.ofCompactSupport u hu.continuous hc,
    BUC.ofCompactSupport (deriv u) hu₁.continuous hc.deriv,
    BUC.ofCompactSupport (deriv (deriv u)) hu₂.continuous hc.deriv.deriv,
    fun z ↦ (hu.differentiable (by simp) z).hasDerivAt,
    fun z ↦ (hu₁.differentiable (by simp) z).hasDerivAt, ?_⟩
  have heq : u =ᶠ[𝓝 0] id := by
    filter_upwards [ρ.eventuallyEq_one] with z hz
    simp only [u, hz, Pi.one_apply, mul_one, id_eq]
  exact ((hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq heq).deriv

/-- Expanding compact cutoffs approximate the linear factor in the
scaling variation. Only the derivatives require uniform bounds. -/
theorem exists_bounded_linear_cutoff_jets :
    ∃ (η η₁ η₂ : ℕ → BUC ℝ ℝ) (C₁ C₂ : ℝ), 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ k z, HasDerivAt (η k) (η₁ k z) z ∧ HasDerivAt (η₁ k) (η₂ k z) z) ∧
      (∀ k z, ‖η₁ k z‖ ≤ C₁ ∧ ‖η₂ k z‖ ≤ C₂) ∧
      ∀ z, Tendsto (fun k ↦ η₁ k z) atTop (𝓝 1) ∧
        Tendsto (fun k ↦ η₂ k z) atTop (𝓝 0) := by
  obtain ⟨u, u₁, u₂, hd, hd₁, hzero⟩ := exists_linear_cutoff_jet
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε1 (k : ℕ) : ε k ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have huc (k : ℕ) : UniformContinuous (fun z : ℝ ↦ ε k * z) :=
    (ContinuousLinearMap.lsmul ℝ ℝ (ε k)).uniformContinuous
  let v := fun k ↦ (ε k)⁻¹ • u.comp (fun z : ℝ ↦ ε k * z) (huc k)
  let v₁ := fun k ↦ u₁.comp (fun z : ℝ ↦ ε k * z) (huc k)
  let v₂ := fun k ↦ ε k • u₂.comp (fun z : ℝ ↦ ε k * z) (huc k)
  refine ⟨v, v₁, v₂, ‖u₁‖, ‖u₂‖, norm_nonneg _, norm_nonneg _, ?_, ?_, ?_⟩
  · intro k z
    constructor
    · convert! ((hd (ε k * z)).comp z ((hasDerivAt_id z).const_mul (ε k))).const_mul (ε k)⁻¹ using 1
      simp only [v₁, BUC.comp_apply, mul_one]
      field_simp [(hε k).ne']
    · simpa only [v₁, v₂, BUC.comp_apply, BUC.smul_apply, smul_eq_mul, mul_one, one_mul, mul_comm,
        Function.comp_def] using!
        (hd₁ (ε k * z)).comp z ((hasDerivAt_id z).const_mul (ε k))
  · intro k z
    refine ⟨u₁.norm_apply_le _, ?_⟩
    change ‖ε k * u₂ (ε k * z)‖ ≤ ‖u₂‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hε k)]
    exact (mul_le_mul_of_nonneg_left (u₂.norm_apply_le _) (hε k).le).trans
      (by simpa using mul_le_mul_of_nonneg_right (hε1 k) (norm_nonneg u₂))
  · intro z
    have hz : Tendsto (fun k ↦ ε k * z) atTop (𝓝 0) := by simpa using hεlim.mul_const z
    constructor
    · simpa only [v₁, BUC.comp_apply, Function.comp_def, hzero] using! (u₁.continuous.tendsto 0).comp hz
    · simpa only [v₂, BUC.smul_apply, BUC.comp_apply, Function.comp_def, smul_eq_mul, zero_mul] using!
        hεlim.mul ((u₂.continuous.tendsto 0).comp hz)

end

end Planarwave
