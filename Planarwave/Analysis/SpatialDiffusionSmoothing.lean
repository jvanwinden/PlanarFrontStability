/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSpatialGenerator
import Planarwave.Analysis.BUCFDerivCoordinates
import Planarwave.Analysis.ConvectiveHeatSmoothingMultidimensional
import Planarwave.Analysis.SemigroupSmoothing

/-!
# Smoothing of the full spatial matrix diffusion semigroup

The paper's diffusion eigenbasis transfers the Gaussian first and second spatial
derivative bounds to the actual principal semigroup. In particular, its generator
after positive-time evolution is bounded, with the short-time bound `C/t`.
No smoothness of the initial BUC datum is assumed.
-/

open Set
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

local instance : NormedAddCommGroup (BUC E (E →L[ℝ] ℂ^n)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] ℂ^n)
local instance : NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℂ^n)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] E →L[ℝ] ℂ^n)
local instance : NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℂ)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] E →L[ℝ] ℂ)

/-- The first two spatial derivatives of the actual matrix heat evolution are BUC,
with the Gaussian `t⁻¹ᐟ²` and `t⁻¹` estimates in the original state coordinates.
The constants are independent of the drift and the positive time. -/
theorem exists_bounded_buc_fderivatives_spatialDiffusion
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    {μ : ℝ} (hμ : 0 < μ) (hμa : ∀ i, μ ≤ diffusionEigenvalues D hD i)
    (b : E) (t : NNReal) (ht : 0 < t) (v : BUC E (ℂ^n)) :
    let K := ‖(diffusionCoordinatesEquiv D hD).toContinuousLinearMap.restrictScalars ℝ‖ *
      ‖(spatialDiffusionBUCCoordinatesEquiv (E := E) D hD).symm.toContinuousLinearMap‖
    ∃ (g : BUC E (E →L[ℝ] ℂ^n)) (h : BUC E (E →L[ℝ] E →L[ℝ] ℂ^n)),
      (∀ x, HasFDerivAt (spatialDiffusionC0Semigroup D hD b t v) (g x) x) ∧
      (∀ x, HasFDerivAt g (h x) x) ∧
      ‖g‖ ≤ K * ‖v‖ / heatScale μ t ∧ ‖h‖ ≤ K * ‖v‖ / (μ * t) := by
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  let L := (diffusionCoordinatesEquiv D hD).toContinuousLinearMap.restrictScalars ℝ
  let f (i : Fin n) := J.symm v i
  let w (i : Fin n) := convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t b (f i)
  have ht' : 0 < (t : ℝ) := ht
  choose g h hg hh hgnorm hhnorm using fun i : Fin n ↦
    exists_bounded_buc_fderivatives_convectiveHeatFlow (hμ.trans_le (hμa i)) ht' b (f i)
  have hgs : ‖g‖ ≤ ‖J.symm v‖ / heatScale μ t := by
    apply (pi_norm_le_iff_of_nonneg (by positivity [heatScale_pos_of_pos hμ ht'])).mpr
    intro i
    have hscale : heatScale μ t ≤ heatScale (diffusionEigenvalues D hD i) t := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hμa i) (by norm_num)) t.2
    exact (hgnorm i).trans ((div_le_div_of_nonneg_left (norm_nonneg (f i))
      (heatScale_pos_of_pos hμ ht') hscale).trans
      (div_le_div_of_nonneg_right (norm_le_pi_norm (J.symm v) i)
        (heatScale_pos_of_pos hμ ht').le))
  have hhs : ‖h‖ ≤ ‖J.symm v‖ / (μ * t) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact (hhnorm i).trans ((div_le_div_of_nonneg_left (norm_nonneg (f i))
      (mul_pos hμ ht') (mul_le_mul_of_nonneg_right (hμa i) t.2)).trans
      (div_le_div_of_nonneg_right (norm_le_pi_norm (J.symm v) i) (by positivity)))
  have hw : spatialDiffusionC0Semigroup D hD b t v = BUC.postcompCLM L (BUC.ofPi w) := by
    ext x
    rfl
  refine ⟨BUC.fderivPostcompPi L g,
    BUC.fderivPostcompPi (BUC.fderivCoordinates (E := E) L) h, ?_, ?_, ?_, ?_⟩
  · rw [hw]
    exact BUC.hasFDerivAt_postcomp_ofPi L w g hg
  · exact BUC.hasFDerivAt_postcomp_ofPi (BUC.fderivCoordinates L) g h hh
  · calc
      ‖BUC.fderivPostcompPi L g‖ ≤ ‖L‖ * ‖g‖ := BUC.norm_fderivPostcompPi_le L g
      _ ≤ ‖L‖ * ((‖J.symm.toContinuousLinearMap‖ * ‖v‖) / heatScale μ t) :=
        mul_le_mul_of_nonneg_left (hgs.trans (div_le_div_of_nonneg_right
          (J.symm.toContinuousLinearMap.le_opNorm v) (heatScale_pos_of_pos hμ ht').le))
          (norm_nonneg L)
      _ = _ := by ring
  · calc
      ‖BUC.fderivPostcompPi (E := E) (F := E →L[ℝ] ℂ) (G := E →L[ℝ] ℂ^n)
          (BUC.fderivCoordinates L) h‖ ≤
          ‖BUC.fderivCoordinates (E := E) L‖ * ‖h‖ :=
        BUC.norm_fderivPostcompPi_le (E := E) (F := E →L[ℝ] ℂ) (G := E →L[ℝ] ℂ^n)
          (BUC.fderivCoordinates L) h
      _ ≤ ‖L‖ * ‖h‖ := mul_le_mul_of_nonneg_right
        (BUC.norm_fderivCoordinates_le L) (norm_nonneg h)
      _ ≤ ‖L‖ * ((‖J.symm.toContinuousLinearMap‖ * ‖v‖) / (μ * t)) :=
        mul_le_mul_of_nonneg_left (hhs.trans (div_le_div_of_nonneg_right
          (J.symm.toContinuousLinearMap.le_opNorm v) (by positivity))) (norm_nonneg L)
      _ = _ := by ring

/-- Gaussian smoothing gives spatial smoothness of every order for the actual
matrix principal evolution, without a regularity assumption on its initial datum. -/
theorem contDiff_spatialDiffusionC0Semigroup
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (b : E) (t : NNReal) (ht : 0 < t) (v : BUC E (ℂ^n)) :
    ContDiff ℝ ∞ (spatialDiffusionC0Semigroup D hD b t v : E → ℂ^n) := by
  obtain ⟨μ, hμ, hμa⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  let L := (diffusionCoordinatesEquiv D hD).toContinuousLinearMap.restrictScalars ℝ
  have heq : (spatialDiffusionC0Semigroup D hD b t v : E → ℂ^n) =
      fun x ↦ L (fun i ↦ heatFlow (diffusionEigenvalues D hD i) t
        (J.symm v i) (x + (t : ℝ) • b)) := by
    funext x
    simp only [spatialDiffusionC0Semigroup_apply, spatialDiffusionBUCCoordinatesEquiv_apply,
      convectiveHeatFlowBUC_apply]
    rfl
  rw [heq]
  apply L.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_infty_heatFlow (hμ.trans_le (hμa i)) (show 0 < (t : ℝ) from ht)
    (J.symm v i)).comp (contDiff_id.add contDiff_const)

/-- Gaussian smoothing puts every positive-time principal orbit in the generator
domain. The generator value is the actual matrix diffusion and drift expression. -/
theorem exists_spatialDiffusion_generator_eq_pde
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (b : E) (t : NNReal) (ht : 0 < t) (v : BUC E (ℂ^n)) :
    ∃ y : BUC E (ℂ^n),
      (spatialDiffusionC0Semigroup D hD b).HasGeneratorAt
        (spatialDiffusionC0Semigroup D hD b t v) y ∧
      ∀ x, y x = frontComplexifiedDiffusion D
          (Δ (spatialDiffusionC0Semigroup D hD b t v : E → ℂ^n) x) +
        fderiv ℝ (spatialDiffusionC0Semigroup D hD b t v) x b := by
  obtain ⟨μ, hμ, hμa⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  choose g h hg hh hgnorm hhnorm using fun i : Fin n ↦
    exists_bounded_buc_fderivatives_convectiveHeatFlow (hμ.trans_le (hμa i))
      (show 0 < (t : ℝ) from ht) b (J.symm v i)
  refine ⟨J (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D hD i) b (g i) (h i)),
    ?_, ?_⟩
  · rw [spatialDiffusionC0Semigroup_apply]
    exact spatialDiffusionC0Semigroup_hasGeneratorAt D hD hDinj b _ g h hg hh
  · intro x
    rw [spatialDiffusionC0Semigroup_apply]
    exact spatialDiffusionGenerator_coordinates D hD b _ g h hg hh x

/-- The short-time generator bound obtained by estimating every diffusion coordinate. -/
theorem exists_spatialDiffusion_generator_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    {μ : ℝ} (hμ : 0 < μ) (hμa : ∀ i, μ ≤ diffusionEigenvalues D hD i)
    (b : E) (t : NNReal) (ht : 0 < t) (ht₁ : t ≤ 1) (v : BUC E (ℂ^n)) :
    ∃ y : BUC E (ℂ^n),
      (spatialDiffusionC0Semigroup D hD b).HasGeneratorAt
        (spatialDiffusionC0Semigroup D hD b t v) y ∧
      (t : ℝ) * ‖y‖ ≤
        (‖(spatialDiffusionBUCCoordinatesEquiv (E := E) D hD).toContinuousLinearMap‖ *
          ‖(spatialDiffusionBUCCoordinatesEquiv (E := E) D hD).symm.toContinuousLinearMap‖) *
          ((Module.finrank ℝ E : ℝ) + ‖b‖ / Real.sqrt (2 * μ)) * ‖v‖ := by
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  let a := diffusionEigenvalues D hD
  let f (i : Fin n) := J.symm v i
  choose g h hg hh hgnorm hhnorm using fun i : Fin n ↦
    exists_bounded_buc_fderivatives_convectiveHeatFlow (hμ.trans_le (hμa i))
      (show 0 < (t : ℝ) from ht) b (f i)
  let z : Fin n → BUC E ℂ := fun i ↦ convectiveGeneratorBUC (a i) b (g i) (h i)
  refine ⟨J z, ?_, ?_⟩
  · rw [spatialDiffusionC0Semigroup_apply]
    exact spatialDiffusionC0Semigroup_hasGeneratorAt D hD hDinj b _ g h hg hh
  have ht' : 0 < (t : ℝ) := ht
  have hz : ‖(t : ℝ) • z‖ ≤
      ((Module.finrank ℝ E : ℝ) + ‖b‖ / Real.sqrt (2 * μ)) * ‖J.symm v‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change ‖(t : ℝ) • z i‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht']
    exact (time_mul_norm_convectiveGeneratorBUC_le hμ (hμa i) ht'
      (show (t : ℝ) ≤ 1 from ht₁) b (f i) (g i) (h i) (hgnorm i) (hhnorm i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (J.symm v) i) (by positivity))
  calc
    (t : ℝ) * ‖J z‖ = ‖J ((t : ℝ) • z)‖ := by
      have heq : J ((t : ℝ) • z) = (t : ℝ) • J z :=
        (J.toContinuousLinearMap.restrictScalars ℝ).map_smul (t : ℝ) z
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht']
    _ ≤ ‖J.toContinuousLinearMap‖ * ‖(t : ℝ) • z‖ := J.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖J.toContinuousLinearMap‖ *
        (((Module.finrank ℝ E : ℝ) + ‖b‖ / Real.sqrt (2 * μ)) *
          (‖J.symm.toContinuousLinearMap‖ * ‖v‖)) :=
      mul_le_mul_of_nonneg_left
        (hz.trans (mul_le_mul_of_nonneg_left (J.symm.toContinuousLinearMap.le_opNorm v)
          (by positivity))) (norm_nonneg J.toContinuousLinearMap)
    _ = _ := by ring

/-- An inverse-time bound for the generator composed with spatial evolution, as a
bounded complex-linear operator on the full spatial BUC space. -/
theorem exists_spatialDiffusion_generator_opNorm_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (b : E) :
    ∃ C > 0, ∀ t : NNReal, 0 < t → t ≤ 1 →
      ∃ B : BUC E (ℂ^n) →L[ℂ] BUC E (ℂ^n),
        (∀ v, (spatialDiffusionC0Semigroup D hD b).HasGeneratorAt
          (spatialDiffusionC0Semigroup D hD b t v) (B v)) ∧ ‖B‖ ≤ C / (t : ℝ) := by
  obtain ⟨μ, hμ, hμa⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  let J := spatialDiffusionBUCCoordinatesEquiv (E := E) D hD
  let C := (‖J.toContinuousLinearMap‖ * ‖J.symm.toContinuousLinearMap‖) *
    ((Module.finrank ℝ E : ℝ) + ‖b‖ / Real.sqrt (2 * μ))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t ht ht₁ ↦ ?_⟩
  apply (spatialDiffusionC0Semigroup D hD b).exists_generatorCompCLM
    (spatialDiffusionC0Semigroup D hD b t) (by positivity)
  intro v
  obtain ⟨y, hy, hb⟩ := exists_spatialDiffusion_generator_bound D hD hDinj hμ hμa b t ht ht₁ v
  refine ⟨y, hy, ?_⟩
  have ht' : 0 < (t : ℝ) := ht
  have hbound : (t : ℝ) * ‖y‖ ≤ max C 1 * ‖v‖ :=
    hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg v))
  rw [div_mul_eq_mul_div, le_div_iff₀ ht']
  nlinarith

/-- The spatial principal semigroup is differentiable in operator norm at positive times. -/
theorem differentiableOn_spatialDiffusionC0Semigroup
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (b : E) :
    DifferentiableOn ℝ (fun t : ℝ ↦ spatialDiffusionC0Semigroup D hD b t.toNNReal) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_spatialDiffusion_generator_opNorm_bound D hD hDinj b
  apply (spatialDiffusionC0Semigroup D hD b).differentiableOn_operator_of_smoothing
  intro t ht ht₁
  obtain ⟨B, hB, _⟩ := hb t ht ht₁
  exact ⟨B, hB⟩

/-- The spatial principal semigroup is smooth in operator norm on the positive real axis. -/
theorem contDiffOn_spatialDiffusionC0Semigroup
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (b : E) :
    ContDiffOn ℝ ∞ (fun t : ℝ ↦ spatialDiffusionC0Semigroup D hD b t.toNNReal) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_spatialDiffusion_generator_opNorm_bound D hD hDinj b
  apply (spatialDiffusionC0Semigroup D hD b).contDiffOn_infty_operator_of_smoothing
  intro t ht ht₁
  obtain ⟨B, hB, _⟩ := hb t ht ht₁
  exact ⟨B, hB⟩

/-- The operator-valued time derivative obeys the short-time parabolic estimate. -/
theorem exists_deriv_spatialDiffusionC0Semigroup_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (b : E) :
    ∃ C > 0, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖deriv (fun s : ℝ ↦ spatialDiffusionC0Semigroup D hD b s.toNNReal) t‖ ≤ C / t := by
  obtain ⟨C, hC, hb⟩ := exists_spatialDiffusion_generator_opNorm_bound D hD hDinj b
  refine ⟨C, hC, fun t ht ht₁ ↦ ?_⟩
  obtain ⟨B, hB, hnorm⟩ := hb ⟨t, ht.le⟩ ht ht₁
  have hdiff := (differentiableOn_spatialDiffusionC0Semigroup D hD hDinj b t ht).differentiableAt
    (isOpen_Ioi.mem_nhds ht)
  have heq : deriv (fun s : ℝ ↦ spatialDiffusionC0Semigroup D hD b s.toNNReal) t = B := by
    apply ContinuousLinearMap.ext
    intro v
    have hd := (spatialDiffusionC0Semigroup D hD b).hasGeneratorAt_of_hasDerivAt_operator ht.le
      hdiff.hasDerivAt v
    rw [Real.toNNReal_of_nonneg ht.le] at hd
    exact hd.unique (hB v)
  rw [heq]
  exact hnorm

/-- The time derivative of the principal evolution acts by the actual spatial PDE
operator on every BUC datum after positive-time smoothing. -/
theorem deriv_spatialDiffusionC0Semigroup_apply
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (b : E) {t : ℝ} (ht : 0 < t) (v : BUC E (ℂ^n)) (x : E) :
    deriv (fun s : ℝ ↦ spatialDiffusionC0Semigroup D hD b s.toNNReal) t v x =
      frontComplexifiedDiffusion D
          (Δ (spatialDiffusionC0Semigroup D hD b t.toNNReal v : E → ℂ^n) x) +
        fderiv ℝ (spatialDiffusionC0Semigroup D hD b t.toNNReal v) x b := by
  have hdiff := (differentiableOn_spatialDiffusionC0Semigroup D hD hDinj b t ht).differentiableAt
    (isOpen_Ioi.mem_nhds ht)
  have hd := (spatialDiffusionC0Semigroup D hD b).hasGeneratorAt_of_hasDerivAt_operator ht.le
    hdiff.hasDerivAt v
  obtain ⟨y, hy, heq⟩ := exists_spatialDiffusion_generator_eq_pde D hD hDinj b t.toNNReal
    (Real.toNNReal_pos.mpr ht) v
  rw [hd.unique hy]
  exact heq x

end

end Planarwave
