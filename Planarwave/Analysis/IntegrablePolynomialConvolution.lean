/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfBounds

@[expose] public section

/-!
# Convolution with the integrable forcing weight

The cases of the paper's convolution estimate needed in Step 1 are
`α = 1/2` and `α = 1`, with forcing exponent `5/4`. Splitting according
to which time is larger gives a sum of two integrable majorants.
-/

open MeasureTheory Set

namespace Planarwave

/-- Exchange the decay exponents when the second base is larger. -/
theorem rpow_neg_mul_rpow_neg_le_swap {a b α γ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hαγ : α ≤ γ) :
    a ^ (-α) * b ^ (-γ) ≤ b ^ (-α) * a ^ (-γ) := by
  have hb : 0 < b := ha.trans_le hab
  have h := Real.rpow_le_rpow_of_nonpos ha hab (sub_nonpos.mpr hαγ)
  calc
    _ = (a ^ (-α) * b ^ (-α)) * b ^ (α - γ) := by
      rw [mul_assoc, ← Real.rpow_add hb]
      congr 2
      ring
    _ ≤ (a ^ (-α) * b ^ (-α)) * a ^ (α - γ) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [mul_right_comm, ← Real.rpow_add ha]
      have he : -α + (α - γ) = -γ := by ring
      rw [he, mul_comm]

/-- One of the two half-intervals controls the slow weight. -/
theorem one_add_rpow_neg_le_half {α s t : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t ≤ 2 * s) :
    (1 + s) ^ (-α) ≤ (2 : ℝ) ^ α * (1 + t) ^ (-α) := by
  calc
    _ = (2 : ℝ) ^ α * (2 * (1 + s)) ^ (-α) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1 + s),
        ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        add_neg_cancel, Real.rpow_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hα))
      (by positivity)

/-- Pointwise two-sided integrable majorant for the convolution kernel. -/
theorem polynomial_convolution_kernel_le {α γ t r : ℝ}
    (hα : 0 ≤ α) (hαγ : α ≤ γ) (hr : r ∈ Icc 0 t) :
    (1 + t - r) ^ (-α) * (1 + r) ^ (-γ) ≤
      ((2 : ℝ) ^ α * (1 + t) ^ (-α)) *
        ((1 + r) ^ (-γ) + (1 + t - r) ^ (-γ)) := by
  have ht : 0 ≤ t := hr.1.trans hr.2
  have ha : 0 < 1 + t - r := by linarith [hr.2]
  have hb : 0 < 1 + r := by linarith [hr.1]
  by_cases hhalf : r ≤ t - r
  · have hw := one_add_rpow_neg_le_half hα (by linarith : 0 ≤ t - r) ht
      (by linarith : t ≤ 2 * (t - r))
    rw [← add_sub_assoc] at hw
    calc
      _ ≤ ((2 : ℝ) ^ α * (1 + t) ^ (-α)) * (1 + r) ^ (-γ) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (by positivity)
  · calc
      _ ≤ (1 + r) ^ (-α) * (1 + t - r) ^ (-γ) :=
        rpow_neg_mul_rpow_neg_le_swap ha (by linarith) hαγ
      _ ≤ ((2 : ℝ) ^ α * (1 + t) ^ (-α)) * (1 + t - r) ^ (-γ) :=
        mul_le_mul_of_nonneg_right (one_add_rpow_neg_le_half hα hr.1 ht (by linarith))
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
        (by positivity)

/-- The integrable `5/4` forcing preserves the slow decay exponent.
In particular this includes both heat-derivative exponents in Step 1. -/
theorem integral_polynomial_convolution_le {α t : ℝ}
    (hα : 0 ≤ α) (hα' : α ≤ (5 : ℝ) / 4) (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, (1 + t - r) ^ (-α) * (1 + r) ^ (-(5 : ℝ) / 4)) ≤
      (8 * (2 : ℝ) ^ α) * (1 + t) ^ (-α) := by
  have hc (p : ℝ) : ContinuousOn (fun r : ℝ ↦ (1 + r) ^ p) (Icc 0 t) :=
    (continuousOn_const.add continuousOn_id).rpow_const
      (fun r hr ↦ Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))
  have hd (p : ℝ) : ContinuousOn (fun r : ℝ ↦ (1 + t - r) ^ p) (Icc 0 t) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun r hr ↦ Or.inl (by change 1 + t - r ≠ 0; linarith [hr.2]))
  have hreflect : (∫ r in (0 : ℝ)..t, (1 + t - r) ^ (-(5 : ℝ) / 4)) =
      ∫ r in (0 : ℝ)..t, (1 + r) ^ (-(5 : ℝ) / 4) := by
    simpa only [add_sub_assoc, sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left (fun r : ℝ ↦ (1 + r) ^ (-(5 : ℝ) / 4)) t
        (a := (0 : ℝ)) (b := t)
  calc
    _ ≤ ∫ r in (0 : ℝ)..t, ((2 : ℝ) ^ α * (1 + t) ^ (-α)) *
        ((1 + r) ^ (-(5 : ℝ) / 4) + (1 + t - r) ^ (-(5 : ℝ) / 4)) :=
      intervalIntegral.integral_mono_on ht
        (((hd (-α)).mul (hc (-(5 : ℝ) / 4))).intervalIntegrable_of_Icc ht)
        ((((hc (-(5 : ℝ) / 4)).add (hd (-(5 : ℝ) / 4))).const_mul _).intervalIntegrable_of_Icc ht)
        (fun r hr ↦ by simpa only [neg_div, Pi.mul_apply] using polynomial_convolution_kernel_le hα hα' hr)
    _ = ((2 : ℝ) ^ α * (1 + t) ^ (-α)) *
        (2 * ∫ r in (0 : ℝ)..t, (1 + r) ^ (-(5 : ℝ) / 4)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        ((hc _).intervalIntegrable_of_Icc ht) ((hd _).intervalIntegrable_of_Icc ht), hreflect]
      ring
    _ ≤ ((2 : ℝ) ^ α * (1 + t) ^ (-α)) * (2 * 4) := by
      gcongr
      exact integral_one_add_rpow_neg_five_quarters_le ht
    _ = _ := by ring

/-- Banach-valued form of the convolution bound, without an unnecessary
integrability hypothesis on the function being estimated. -/
theorem norm_integral_le_polynomial_convolution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {α A t : ℝ} (hα : 0 ≤ α) (hα' : α ≤ (5 : ℝ) / 4)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (v : ℝ → F)
    (hv : ∀ r ∈ Icc 0 t, ‖v r‖ ≤
      A * ((1 + t - r) ^ (-α) * (1 + r) ^ (-(5 : ℝ) / 4))) :
    ‖∫ r in (0 : ℝ)..t, v r‖ ≤ (8 * (2 : ℝ) ^ α) * A * (1 + t) ^ (-α) := by
  have hb : ContinuousOn (fun r : ℝ ↦
      A * ((1 + t - r) ^ (-α) * (1 + r) ^ (-(5 : ℝ) / 4))) (Icc 0 t) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.mul
    · exact (continuousOn_const.sub continuousOn_id).rpow_const
        (fun r hr ↦ Or.inl (by change 1 + t - r ≠ 0; linarith [hr.2]))
    · exact (continuousOn_const.add continuousOn_id).rpow_const
        (fun r hr ↦ Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))
  calc
    _ ≤ ∫ r in (0 : ℝ)..t, A * ((1 + t - r) ^ (-α) * (1 + r) ^ (-(5 : ℝ) / 4)) := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht
      · filter_upwards [] with r hr
        exact hv r ⟨hr.1.le, hr.2⟩
      · exact hb.intervalIntegrable_of_Icc ht
    _ = A * ∫ r in (0 : ℝ)..t, (1 + t - r) ^ (-α) * (1 + r) ^ (-(5 : ℝ) / 4) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ A * ((8 * (2 : ℝ) ^ α) * (1 + t) ^ (-α)) :=
      mul_le_mul_of_nonneg_left (integral_polynomial_convolution_le hα hα' ht) hA
    _ = _ := by ring

end Planarwave
