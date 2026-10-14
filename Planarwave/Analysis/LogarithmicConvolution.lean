/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The borderline time convolution in the remainder estimate

The `α = γ = 1` case of the paper's `lem:convolution` is the estimate
used in Step 3a of `lem:key`. Partial fractions give the exact integral,
and hence the `(1+t)⁻¹ log(2+t)` bound for the Duhamel remainder.
-/

open MeasureTheory Set

namespace Planarwave

/-- Continuity of the nonsingular borderline convolution kernel. -/
theorem continuousOn_one_add_inv_convolution {t : ℝ} :
    ContinuousOn (fun r : ℝ ↦ (1 + t - r)⁻¹ * (1 + r)⁻¹) (Icc 0 t) :=
  ((continuousOn_const.sub continuousOn_id).inv₀ (fun r hr ↦ by
    change 1 + t - r ≠ 0
    linarith [hr.2])).mul
    ((continuousOn_const.add continuousOn_id).inv₀ (fun r hr ↦ by
      change 1 + r ≠ 0
      linarith [hr.1]))

/-- The exact borderline time convolution, obtained by partial fractions. -/
theorem integral_one_add_inv_convolution {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, (1 + t - r)⁻¹ * (1 + r)⁻¹) =
      (2 / (2 + t)) * Real.log (1 + t) := by
  have hden : 2 + t ≠ 0 := by linarith
  have hd : ∀ r ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ ↦ (Real.log (1 + s) - Real.log (1 + t - s)) / (2 + t))
        ((1 + t - r)⁻¹ * (1 + r)⁻¹) r := by
    intro r hr
    rw [uIcc_of_le ht] at hr
    have h₁ : 1 + r ≠ 0 := by linarith [hr.1]
    have h₂ : 1 + t - r ≠ 0 := by linarith [hr.2]
    have h := ((((hasDerivAt_id r).const_add 1).log h₁).sub
      (((hasDerivAt_const r (1 + t)).sub (hasDerivAt_id r)).log h₂)).div_const (2 + t)
    convert! h using 1
    simp only [id_eq, Pi.sub_apply]
    field_simp
    ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuousOn_one_add_inv_convolution.intervalIntegrable_of_Icc ht)
  rw [heq]
  simp only [add_sub_cancel_right, add_zero, sub_zero, Real.log_one]
  ring

/-- The logarithmic bound used to estimate the stable remainder. -/
theorem integral_one_add_inv_convolution_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, (1 + t - r)⁻¹ * (1 + r)⁻¹) ≤
      (2 / (1 + t)) * Real.log (2 + t) := by
  rw [integral_one_add_inv_convolution ht]
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  · exact Real.log_le_log (by linarith) (by linarith)
  · exact Real.log_nonneg (by linarith)
  · positivity

/-- Banach-valued Duhamel terms bounded by this kernel have the same
logarithmic decay. The source may be vector- or operator-valued. -/
theorem norm_integral_le_logarithmic_convolution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) (v : ℝ → F)
    (hv : ∀ r ∈ Icc 0 t, ‖v r‖ ≤ A * ((1 + t - r)⁻¹ * (1 + r)⁻¹)) :
    ‖∫ r in (0 : ℝ)..t, v r‖ ≤ (2 * A / (1 + t)) * Real.log (2 + t) := by
  calc
    _ ≤ ∫ r in (0 : ℝ)..t, A * ((1 + t - r)⁻¹ * (1 + r)⁻¹) := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht
      · filter_upwards [] with r hr
        exact hv r ⟨hr.1.le, hr.2⟩
      · exact (continuousOn_one_add_inv_convolution.const_mul A).intervalIntegrable_of_Icc ht
    _ = A * ∫ r in (0 : ℝ)..t, (1 + t - r)⁻¹ * (1 + r)⁻¹ := intervalIntegral.integral_const_mul _ _
    _ ≤ A * ((2 / (1 + t)) * Real.log (2 + t)) :=
      mul_le_mul_of_nonneg_left (integral_one_add_inv_convolution_le ht) hA
    _ = _ := by ring

/-- Include the initial remainder term, absorbing its faster decay in
the same logarithmic envelope used in `eq:west`. -/
theorem norm_add_integral_le_logarithmic_convolution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) (x : F) (v : ℝ → F)
    (hx : ‖x‖ ≤ A / (1 + t))
    (hv : ∀ r ∈ Icc 0 t, ‖v r‖ ≤ A * ((1 + t - r)⁻¹ * (1 + r)⁻¹)) :
    ‖x + ∫ r in (0 : ℝ)..t, v r‖ ≤ (4 * A / (1 + t)) * Real.log (2 + t) := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log (2 + t) := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono : Real.log 2 ≤ Real.log (2 + t) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at htwo
    linarith
  have hbase : A / (1 + t) ≤ (2 * A / (1 + t)) * Real.log (2 + t) := by
    calc
      _ = (2 * A / (1 + t)) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  calc
    _ ≤ ‖x‖ + ‖∫ r in (0 : ℝ)..t, v r‖ := norm_add_le _ _
    _ ≤ A / (1 + t) + (2 * A / (1 + t)) * Real.log (2 + t) :=
      add_le_add hx (norm_integral_le_logarithmic_convolution ht hA v hv)
    _ ≤ (2 * A / (1 + t)) * Real.log (2 + t) +
        (2 * A / (1 + t)) * Real.log (2 + t) := add_le_add hbase le_rfl
    _ = _ := by ring

end Planarwave
