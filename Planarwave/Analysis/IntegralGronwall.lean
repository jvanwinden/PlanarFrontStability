/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Integral Grönwall with a time-dependent coefficient

The forcing in Lemma `lem:xiAP` has integrable time decay. Keeping its
time-dependent coefficient inside the exponential gives a bound independent
of the final time, unlike the constant-coefficient Grönwall estimate.
-/

open MeasureTheory Set

namespace Planarwave

/-- Integral Grönwall on a compact time interval, proved by an integrating
factor. No sign assumption on the function being bounded is needed. -/
theorem le_exp_integral_of_le_add_integral_mul
    {u b : ℝ → ℝ} {A T : ℝ} (hT : 0 ≤ T)
    (hu : ContinuousOn u (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hb0 : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (hi : ∀ t ∈ Icc 0 T, u t ≤ A + ∫ r in (0 : ℝ)..t, b r * u r) :
    ∀ t ∈ Icc 0 T, u t ≤ A * Real.exp (∫ r in (0 : ℝ)..t, b r) := by
  let B := fun t ↦ ∫ r in (0 : ℝ)..t, b r
  let U := fun t ↦ A + ∫ r in (0 : ℝ)..t, b r * u r
  have hbint : IntervalIntegrable b volume 0 T :=
    (hb.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hbuint : IntervalIntegrable (fun r ↦ b r * u r) volume 0 T :=
    ((hb.mul hu).mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hBc : ContinuousOn B (Icc 0 T) := by
    simpa [B, uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hbint (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
  have hUc : ContinuousOn U (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hbuint
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
    simpa [U, uIcc_of_le hT] using! continuousOn_const.add this
  have hderiv : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s ↦ Real.exp (-B s) * U s)
        (Real.exp (-B t) * b t * (u t - U t)) t := by
    intro t ht
    have hnhds : Icc (0 : ℝ) T ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hBt : HasDerivAt B (b t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hbint.mono_set (by rw [uIcc_of_le ht.1.le, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2.le))
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          (hb.mono Ioo_subset_Icc_self) t ht)
        (hb.continuousAt hnhds)
    have hUt : HasDerivAt U (b t * u t) t :=
      (intervalIntegral.integral_hasDerivAt_right
        (hbuint.mono_set (by rw [uIcc_of_le ht.1.le, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2.le))
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          ((hb.mul hu).mono Ioo_subset_Icc_self) t ht)
        ((hb.mul hu).continuousAt hnhds)).const_add A
    convert! hBt.neg.exp.mul hUt using 1
    simp only [Pi.neg_apply]
    ring
  have hmono : AntitoneOn (fun t ↦ Real.exp (-B t) * U t) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      ((Real.continuous_exp.comp_continuousOn hBc.neg).mul hUc)
    · intro t ht
      exact (hderiv t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      change deriv (fun s ↦ Real.exp (-B s) * U s) t ≤ 0
      rw [(hderiv t ht').deriv]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Real.exp_pos _).le (hb0 t (Ioo_subset_Icc_self ht')))
        (sub_nonpos.mpr (hi t (Ioo_subset_Icc_self ht')))
  intro t ht
  have h := hmono ⟨le_refl 0, hT⟩ ht ht.1
  have hbound : Real.exp (-B t) * U t ≤ A := by simpa [B, U] using h
  have hcancel : Real.exp (B t) * Real.exp (-B t) = 1 := by
    rw [← Real.exp_add]; simp
  have hscaled := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (B t)).le
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  exact (hi t ht).trans (hscaled.trans_eq (mul_comm _ _))

end Planarwave
