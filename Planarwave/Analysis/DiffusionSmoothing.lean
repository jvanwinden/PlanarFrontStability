/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionSemigroup
import all Planarwave.Analysis.DiffusionEigenbasis
import all Planarwave.Analysis.FrontCoefficient
import Planarwave.Analysis.ConvectiveHeatSmoothing
import Planarwave.Analysis.SemigroupSmoothing

/-!
# The short-time generator estimate for the principal diffusion semigroup

We retain the paper's eigenbasis construction. Scalar Gaussian derivative bounds give
`t ‖A_q S_q(t)‖ ≤ C` on `0 < t ≤ 1`, with `C` independent of the nonnegative parameter `q`.
This is the quantitative smoothing input for the analytic-semigroup argument in Section 2;
analyticity and the spectral-bound/growth-bound theorem are not assumed here.
-/

namespace Planarwave

noncomputable section

open Set
open scoped ContDiff

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} [Nontrivial (ℝ^n)]

omit [Nontrivial (ℝ^n)] in
/-- The diagonal scalar estimate transported to the actual principal differential operator. -/
theorem exists_frontDiffusionFlowBUC_generator_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    {μ : ℝ} (hμ : 0 < μ) (hμa : ∀ i, μ ≤ diffusionEigenvalues D hD i)
    (c : ℝ) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 < t) (ht₁ : t ≤ 1)
    (v : BUC ℝ (ℂ^n)) :
    ∃ w : ComplexBUC2 (ℂ^n),
      ComplexBUC2.value (ℂ^n) w = frontDiffusionFlowBUC D hD c q t v ∧
      t * ‖longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 w‖ ≤
        (‖(diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap‖ *
          ‖(diffusionBUCCoordinatesEquiv D hD).symm.toContinuousLinearMap‖) *
          (2 + |c| / Real.sqrt (2 * μ)) * ‖v‖ := by
  let J := diffusionBUCCoordinatesEquiv D hD
  let a := diffusionEigenvalues D hD
  let r (i : Fin n) : ℝ := Real.exp ((-q * a i) * t)
  let f (i : Fin n) := J.symm v i
  choose g h hg hh using fun i : Fin n ↦
    exists_buc_derivatives_convectiveHeatFlow (hμ.trans_le (hμa i)) ht c (f i)
  let w : ComplexBUC2 (ℂ^n) :=
    ⟨((J (fun i ↦ r i • convectiveHeatFlowBUC (a i) t c (f i)),
        J (fun i ↦ r i • g i)), J (fun i ↦ r i • h i)), fun x ↦
      ⟨hasDerivAt_diffusionBUCCoordinatesEquiv D hD _ _
        (fun i y ↦ (hg i y).const_smul (r i)) x,
       hasDerivAt_diffusionBUCCoordinatesEquiv D hD _ _
        (fun i y ↦ (hh i y).const_smul (r i)) x⟩⟩
  refine ⟨w, ?_, ?_⟩
  · change J _ = J _
    congr 1
  let z : Fin n → BUC ℝ ℂ := fun i ↦ r i •
    (a i • h i + c • g i - (q * a i) • convectiveHeatFlowBUC (a i) t c (f i))
  have hop : longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 w =
      J z := by
    rw [← diffusion_generator_coordinates D hD c q w]
    change J (fun i ↦ a i • (J.symm (J (fun j ↦ r j • h j)) i) +
      c • (J.symm (J (fun j ↦ r j • g j)) i) -
      (q * a i) • (J.symm (J (fun j ↦ r j • convectiveHeatFlowBUC (a j) t c (f j))) i)) = J z
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    congr 1
    funext i
    dsimp only [z]
    simp only [smul_sub, smul_add, smul_smul]
    rw [mul_comm (a i), mul_comm c, mul_comm (q * a i)]
  have hz : ‖t • z‖ ≤ (2 + |c| / Real.sqrt (2 * μ)) * ‖J.symm v‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change ‖t • z i‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact (time_mul_norm_dampedConvectiveHeat_generator_le hμ (hμa i) ht ht₁ hq c
      (f i) (g i) (h i) (hg i) (hh i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (J.symm v) i) (by positivity))
  rw [hop]
  calc
    t * ‖J z‖ = ‖J (t • z)‖ := by
      have heq : J (t • z) = t • J z := (J.toContinuousLinearMap.restrictScalars ℝ).map_smul t z
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    _ ≤ ‖J.toContinuousLinearMap‖ * ‖t • z‖ := J.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖J.toContinuousLinearMap‖ * ((2 + |c| / Real.sqrt (2 * μ)) *
        (‖J.symm.toContinuousLinearMap‖ * ‖v‖)) := by
      exact mul_le_mul_of_nonneg_left
        (hz.trans (mul_le_mul_of_nonneg_left (J.symm.toContinuousLinearMap.le_opNorm v)
          (by positivity))) (norm_nonneg J.toContinuousLinearMap)
    _ = _ := by ring

/-- A uniform short-time generator bound, with no regularity assumption on the initial datum. -/
theorem exists_uniform_frontDiffusion_generator_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c : ℝ) :
    ∃ C > 0, ∀ q : ℝ, 0 ≤ q → ∀ t : NNReal, 0 < t → t ≤ 1 →
      ∀ v : BUC ℝ (ℂ^n), ∃ y : BUC ℝ (ℂ^n),
        (frontDiffusionC0Semigroup D hD c q).HasGeneratorAt
          (frontDiffusionC0Semigroup D hD c q t v) y ∧
        (t : ℝ) * ‖y‖ ≤ C * ‖v‖ := by
  obtain ⟨μ, hμ, hμa⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  let C := (‖(diffusionBUCCoordinatesEquiv D hD).toContinuousLinearMap‖ *
    ‖(diffusionBUCCoordinatesEquiv D hD).symm.toContinuousLinearMap‖) *
      (2 + |c| / Real.sqrt (2 * μ))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro q hq t ht ht₁ v
  obtain ⟨w, hw, hb⟩ := exists_frontDiffusionFlowBUC_generator_bound D hD hμ hμa c hq
    (show 0 < (t : ℝ) from ht) (show (t : ℝ) ≤ 1 from ht₁) v
  refine ⟨longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 w, ?_, ?_⟩
  · rw [frontDiffusionC0Semigroup_apply, ← hw]
    exact frontDiffusionC0Semigroup_hasGeneratorAt D hD hDinj c q w
  · exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg v))

/-- The generator after positive-time evolution is a bounded operator, with a uniform
inverse-time norm bound for all real nonnegative Fourier parameters. -/
theorem exists_uniform_frontDiffusion_generator_opNorm_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c : ℝ) :
    ∃ C > 0, ∀ q : ℝ, 0 ≤ q → ∀ t : NNReal, 0 < t → t ≤ 1 →
      ∃ B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n),
        (∀ v, (frontDiffusionC0Semigroup D hD c q).HasGeneratorAt
          (frontDiffusionC0Semigroup D hD c q t v) (B v)) ∧ ‖B‖ ≤ C / (t : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_frontDiffusion_generator_bound D hD hDinj c
  refine ⟨C, hC, fun q hq t ht ht₁ ↦ ?_⟩
  apply (frontDiffusionC0Semigroup D hD c q).exists_generatorCompCLM
    (frontDiffusionC0Semigroup D hD c q t) (by positivity)
  intro v
  obtain ⟨y, hy, hnorm⟩ := hb q hq t ht ht₁ v
  refine ⟨y, hy, ?_⟩
  have ht' : 0 < (t : ℝ) := ht
  rw [div_mul_eq_mul_div, le_div_iff₀ ht']
  nlinarith

/-- The principal matrix heat semigroup is differentiable in operator norm at every
positive time, for every nonnegative real Fourier parameter. -/
theorem differentiableOn_frontDiffusionC0Semigroup
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    DifferentiableOn ℝ (fun t : ℝ ↦ frontDiffusionC0Semigroup D hD c q t.toNNReal) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_frontDiffusion_generator_opNorm_bound D hD hDinj c
  apply (frontDiffusionC0Semigroup D hD c q).differentiableOn_operator_of_smoothing
  intro r hr hr₁
  obtain ⟨B, hB, _⟩ := hb q hq r hr hr₁
  exact ⟨B, hB⟩

/-- The principal matrix semigroup is smooth in the operator norm on the positive
real time axis. Complex-time analyticity requires a further argument. -/
theorem contDiffOn_frontDiffusionC0Semigroup
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ContDiffOn ℝ ∞ (fun t : ℝ ↦ frontDiffusionC0Semigroup D hD c q t.toNNReal) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_frontDiffusion_generator_opNorm_bound D hD hDinj c
  apply (frontDiffusionC0Semigroup D hD c q).contDiffOn_infty_operator_of_smoothing
  intro r hr hr₁
  obtain ⟨B, hB, _⟩ := hb q hq r hr hr₁
  exact ⟨B, hB⟩

/-- The actual operator-valued time derivative obeys the short-time parabolic bound.
The constant is chosen before the frequency and time. -/
theorem exists_uniform_deriv_frontDiffusionC0Semigroup_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c : ℝ) :
    ∃ C > 0, ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖deriv (fun s : ℝ ↦ frontDiffusionC0Semigroup D hD c q s.toNNReal) t‖ ≤ C / t := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_frontDiffusion_generator_opNorm_bound D hD hDinj c
  refine ⟨C, hC, fun q hq t ht ht₁ ↦ ?_⟩
  obtain ⟨B, hB, hnorm⟩ := hb q hq ⟨t, ht.le⟩ ht ht₁
  have hdiff := (differentiableOn_frontDiffusionC0Semigroup D hD hDinj c hq t ht).differentiableAt
    (isOpen_Ioi.mem_nhds ht)
  have heq : deriv (fun s : ℝ ↦ frontDiffusionC0Semigroup D hD c q s.toNNReal) t = B := by
    apply ContinuousLinearMap.ext
    intro v
    have hd := (frontDiffusionC0Semigroup D hD c q).hasGeneratorAt_of_hasDerivAt_operator ht.le
      hdiff.hasDerivAt v
    rw [Real.toNNReal_of_nonneg ht.le] at hd
    exact hd.unique (hB v)
  rw [heq]
  exact hnorm

/-- The time derivative just constructed acts by the exact principal differential
expression on the smoothed datum, not merely by an abstract generator extension. -/
theorem deriv_frontDiffusionC0Semigroup_apply
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c : ℝ) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 < t)
    (v : BUC ℝ (ℂ^n)) (w : ComplexBUC2 (ℂ^n))
    (hw : ComplexBUC2.value (ℂ^n) w = frontDiffusionFlowBUC D hD c q t v) :
    deriv (fun s : ℝ ↦ frontDiffusionC0Semigroup D hD c q s.toNNReal) t v =
      longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 w := by
  have hdiff := (differentiableOn_frontDiffusionC0Semigroup D hD hDinj c hq t ht).differentiableAt
    (isOpen_Ioi.mem_nhds ht)
  have hd := (frontDiffusionC0Semigroup D hD c q).hasGeneratorAt_of_hasDerivAt_operator ht.le
    hdiff.hasDerivAt v
  rw [frontDiffusionC0Semigroup_apply, Real.coe_toNNReal t ht.le, ← hw] at hd
  exact hd.unique (frontDiffusionC0Semigroup_hasGeneratorAt D hD hDinj c q w)

end

end Planarwave
