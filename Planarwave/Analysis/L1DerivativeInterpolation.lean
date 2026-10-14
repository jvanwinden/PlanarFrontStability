/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-!
# L1 interpolation for longitudinal derivatives

The estimate `‖u'‖₁ ≤ (2/ε) ‖u‖₁ + ε ‖u''‖₁` follows by integrating the
Taylor remainder over translates of a fixed interval. Its small coefficient
on the second derivative allows the drift in the adjoint ODE to be absorbed.
-/

open MeasureTheory Set

namespace Planarwave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local interpolation estimate with an integral, rather than a supremum,
of the second derivative. -/
theorem mul_norm_firstDerivative_le (u v w : ℝ → F)
    (hv : Continuous v) (hw : Continuous w)
    (huv : ∀ x, HasDerivAt u (v x) x) (hvw : ∀ x, HasDerivAt v (w x) x)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ε * ‖v x‖ ≤ ‖u (x + ε)‖ + ‖u x‖ + ε * ∫ t in x..x + ε, ‖w t‖ := by
  let B := ∫ t in x..x + ε, ‖w t‖
  have hdiff (y : ℝ) (hy : y ∈ Icc x (x + ε)) : ‖v y - v x‖ ≤ B := by
    calc
      _ ≤ ∫ t in x..y, ‖w t‖ :=
        norm_sub_le_integral_of_norm_deriv_le_of_le hy.1 hv.continuousOn
          (fun z _ ↦ (hvw z).differentiableAt.differentiableWithinAt)
          (ae_of_all _ fun z _ ↦ by rw [(hvw z).deriv]) (hw.norm.intervalIntegrable _ _)
      _ ≤ B := intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
        (ae_of_all _ fun z ↦ norm_nonneg _) (hw.norm.intervalIntegrable _ _)
  have hd (y : ℝ) : HasDerivAt (fun z ↦ u z - (z - x) • v x) (v y - v x) y := by
    simpa only [one_smul] using!
      (huv y).sub (((hasDerivAt_id y).sub_const x).smul_const (v x))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y (_ : y ∈ Icc x (x + ε)) ↦ (hd y).hasDerivWithinAt)
    (fun y (hy : y ∈ Ico x (x + ε)) ↦ hdiff y ⟨hy.1, hy.2.le⟩)
    (x + ε) (show x + ε ∈ Icc x (x + ε) from ⟨by linarith, le_rfl⟩)
  simp only [add_sub_cancel_left, sub_self, zero_smul, sub_zero] at hm
  calc
    _ = ‖ε • v x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    _ = ‖(u (x + ε) - u x) - (u (x + ε) - ε • v x - u x)‖ := by congr 1; abel
    _ ≤ ‖u (x + ε) - u x‖ + ‖u (x + ε) - ε • v x - u x‖ := norm_sub_le _ _
    _ ≤ (‖u (x + ε)‖ + ‖u x‖) + B * ε := add_le_add (norm_sub_le _ _) hm
    _ = _ := by dsimp [B]; ring

omit [NormedSpace ℝ F] in
/-- Fubini for the translated finite-interval averages used in L1 interpolation. -/
theorem integrable_norm_translate_interval_prod {w : ℝ → F}
    (hw : Continuous w) (hi : Integrable w) (ε : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ ‖w (p.1 + p.2)‖)
      (volume.prod (volume.restrict (Ioc 0 ε))) := by
  apply (integrable_prod_iff'
    (hw.norm.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun t ↦ hi.norm.comp_add_right t, ?_⟩
  simpa only [Function.comp_def, Pi.add_apply, norm_norm,
    integral_add_right_eq_self (fun x ↦ ‖w x‖)] using
    (integrable_const (μ := volume.restrict (Ioc 0 ε)) (∫ x, ‖w x‖))

omit [NormedSpace ℝ F] in
/-- The total mass of the translated interval averages is interval length
times the original mass. -/
theorem integral_norm_translate_interval {w : ℝ → F}
    (hw : Continuous w) (hi : Integrable w) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ x, ∫ t in Ioc 0 ε, ‖w (x + t)‖) = ε * ∫ x, ‖w x‖ := by
  rw [integral_integral_swap (integrable_norm_translate_interval_prod hw hi ε)]
  simp only [integral_add_right_eq_self (fun x ↦ ‖w x‖), setIntegral_const,
    Real.volume_real_Ioc, sub_zero, smul_eq_mul, max_eq_left hε]

/-- L1 interpolation with an arbitrarily small coefficient on the second derivative. -/
theorem integral_norm_firstDerivative_le (u v w : ℝ → F)
    (hv : Continuous v) (hw : Continuous w)
    (huv : ∀ x, HasDerivAt u (v x) x) (hvw : ∀ x, HasDerivAt v (w x) x)
    (hu : Integrable u) (hvi : Integrable v) (hwi : Integrable w)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x, ‖v x‖) ≤ (2 / ε) * (∫ x, ‖u x‖) + ε * ∫ x, ‖w x‖ := by
  let B := fun x ↦ ∫ t in Ioc 0 ε, ‖w (x + t)‖
  have hBi : Integrable B := (integrable_norm_translate_interval_prod hw hwi ε).integral_prod_left
  have hsum : Integrable (fun x ↦ ‖u (x + ε)‖ + ‖u x‖) :=
    (hu.norm.comp_add_right ε).add hu.norm
  have hB (x : ℝ) : B x = ∫ t in x..x + ε, ‖w t‖ := by
    rw [show B x = ∫ t in 0..ε, ‖w (x + t)‖ from
      (intervalIntegral.integral_of_le hε.le).symm]
    simpa only [add_zero, add_comm ε x] using
      intervalIntegral.integral_comp_add_left (a := 0) (b := ε) (fun t ↦ ‖w t‖) x
  have hb : ε * (∫ x, ‖v x‖) ≤
      2 * (∫ x, ‖u x‖) + ε * (ε * ∫ x, ‖w x‖) := by
    calc
      _ = ∫ x, ε * ‖v x‖ := (integral_const_mul _ _).symm
      _ ≤ ∫ x, (‖u (x + ε)‖ + ‖u x‖) + ε * B x := by
        apply integral_mono (hvi.norm.const_mul ε)
          (hsum.add (hBi.const_mul ε))
        intro x
        change ε * ‖v x‖ ≤ ‖u (x + ε)‖ + ‖u x‖ + ε * B x
        rw [hB]
        exact mul_norm_firstDerivative_le u v w hv hw huv hvw hε x
      _ = _ := by
        rw [integral_add hsum (hBi.const_mul ε),
          integral_add (hu.norm.comp_add_right ε) hu.norm, integral_const_mul,
          integral_add_right_eq_self (fun x ↦ ‖u x‖),
          integral_norm_translate_interval hw hwi hε.le]
        ring
  apply le_of_mul_le_mul_left (a := ε) _ hε
  calc
    _ ≤ _ := hb
    _ = ε * ((2 / ε) * (∫ x, ‖u x‖) + ε * ∫ x, ‖w x‖) := by field_simp

end Planarwave
