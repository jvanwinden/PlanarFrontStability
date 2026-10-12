/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HolomorphicIntegral
public import Planarwave.Analysis.SemigroupRotation

@[expose] public section

/-!
# Quantitative generator smoothing from analytic generation

Cauchy's estimate on a disk whose radius is proportional to the positive time
gives `‖A S(t)‖ ≤ C/t` for short times. The generator is identified using the
actual real semigroup, so the result also applies after bounded perturbation.
-/

open Filter Set Topology

namespace C0Semigroup

noncomputable section

open Planarwave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Exponentially bounded holomorphic time sectors imply the usual short-time
generator estimate, with a constant independent of the time and initial datum. -/
theorem exists_generator_opNorm_bound_of_holomorphic_sector (S : C0Semigroup ℂ E)
    {η M κ : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) (hM : 0 < M) (hκ : 0 ≤ κ)
    {G : ℂ → (E →L[ℂ] E)} (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    (hb : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (κ * ‖z‖)) :
    ∃ C > 0, ∀ t : NNReal, 0 < t → t ≤ 1 →
      ∃ B : E →L[ℂ] E, (∀ v, S.HasGeneratorAt (S t v) (B v)) ∧ ‖B‖ ≤ C / (t : ℝ) := by
  refine ⟨4 * (M * Real.exp (2 * κ)) / η, by positivity, fun t ht ht₁ ↦ ?_⟩
  have ht' : 0 < (t : ℝ) := ht
  have ht₁' : (t : ℝ) ≤ 1 := ht₁
  let r := η * (t : ℝ) / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hsub : Metric.ball (t : ℂ) (2 * r) ⊆ complexTimeSector η := by
    intro z hz
    have hdist : ‖z - (t : ℂ)‖ < η * (t : ℝ) / 2 := by
      have := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at this
      dsimp [r] at this
      linarith
    have hre : |z.re - (t : ℝ)| ≤ ‖z - (t : ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm (z - (t : ℂ))
    have him : |z.im| ≤ ‖z - (t : ℂ)‖ := by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using Complex.abs_im_le_norm (z - (t : ℂ))
    have htime : (t : ℝ) / 2 < z.re := by
      have hηt := mul_le_mul_of_nonneg_right hη₁ t.2
      have habs := neg_le_abs (z.re - (t : ℝ))
      nlinarith
    refine ⟨by linarith, ?_⟩
    exact (him.trans_lt hdist).trans (by nlinarith [mul_lt_mul_of_pos_left htime hη])
  have hbound : ∀ z ∈ Metric.ball (t : ℂ) (2 * r), ‖G z‖ ≤ M * Real.exp (2 * κ) := by
    intro z hz
    have hdist := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hdist
    have hzNorm : ‖z‖ ≤ 2 := by
      have htriangle := norm_add_le (z - (t : ℂ)) (t : ℂ)
      rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht'] at htriangle
      have hηt := mul_le_mul_of_nonneg_right hη₁ t.2
      dsimp [r] at hdist
      nlinarith
    exact (hb z (hsub hz)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hzNorm hκ])) hM.le)
  refine ⟨deriv G (t : ℂ), ?_, ?_⟩
  · intro v
    have h := S.hasGeneratorAt_holomorphicSectorExtension hη hG hreal
      (mem_complexTimeSector_real hη ht') v
    simpa [hreal (t : ℝ) ht'] using h
  · calc
      ‖deriv G (t : ℂ)‖ ≤ (M * Real.exp (2 * κ)) / r :=
        norm_deriv_le_of_bounded_ball hr (hG.mono hsub) hbound (Metric.mem_ball_self hr)
      _ = _ := by dsimp [r]; field_simp

end

end C0Semigroup
