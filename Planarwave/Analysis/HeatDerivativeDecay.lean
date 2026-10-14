/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingSecondDerivative
public import Planarwave.Analysis.IntegrablePolynomialConvolution
public import Planarwave.Analysis.HeatDuhamelDerivative

@[expose] public section

/-!
# Nonsingular decay bounds for heat derivatives

Combine contractivity on differentiated data at short times with heat
smoothing at long times. Applying the integrable convolution estimate
then gives the two weighted derivative bounds used in Step 1 of the paper.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

/-- A uniform estimate and a singular smoothing estimate combine into
a nonsingular polynomial bound, including at time zero. -/
theorem le_one_add_rpow_neg_of_uniform_of_smoothing {u M K p t : ℝ}
    (hM : 0 ≤ M) (hp : 0 ≤ p) (ht : 0 ≤ t) (hu : u ≤ M)
    (hs : 0 < t → u ≤ K * M * t ^ (-p)) :
    u ≤ ((2 : ℝ) ^ p * max 1 K) * M * (1 + t) ^ (-p) := by
  have hK : 0 ≤ max 1 K := le_trans (by norm_num) (le_max_left _ _)
  by_cases ht1 : t ≤ 1
  · have hw : 1 ≤ (2 : ℝ) ^ p * (1 + t) ^ (-p) := by
      calc
        1 = (2 : ℝ) ^ p * (2 : ℝ) ^ (-p) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hp))
          (by positivity)
    calc
      u ≤ M := hu
      _ ≤ M * ((2 : ℝ) ^ p * (1 + t) ^ (-p)) := by nlinarith
      _ ≤ (max 1 K * M) * ((2 : ℝ) ^ p * (1 + t) ^ (-p)) := by
        gcongr
        exact (one_mul M).symm.le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
      _ = _ := by ring
  · have htpos : 0 < t := by linarith
    have hw : t ^ (-p) ≤ (2 : ℝ) ^ p * (1 + t) ^ (-p) := by
      calc
        _ = (2 : ℝ) ^ p * (2 * t) ^ (-p) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht,
            ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            add_neg_cancel, Real.rpow_zero, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hp))
          (by positivity)
    calc
      u ≤ K * M * t ^ (-p) := hs htpos
      _ ≤ max 1 K * M * t ^ (-p) := by gcongr; exact le_max_right _ _
      _ ≤ max 1 K * M * ((2 : ℝ) ^ p * (1 + t) ^ (-p)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hK hM)
      _ = _ := by ring

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance heatDecayFirstBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] F)) := inferInstance
local instance heatDecayFirstBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] F)) := inferInstance
local instance heatDecaySecondTensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance heatDecaySecondTensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance heatDecaySecondBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] F)) := inferInstance
local instance heatDecaySecondBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] F)) := inferInstance

/-- Smoothing applied to an existing first derivative. -/
theorem norm_heatFlow_fderivative_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (q : BUC E (E →L[ℝ] F))
    (hd : ∀ x, HasFDerivAt f (q x) x) :
    ‖heatFlowBUC a t q‖ ≤ ‖f‖ / heatScale a t := by
  have heq : heatFlowBUC a t q = heatFDerivBUC ha ht f := by
    ext x : 1
    exact (hasFDerivAt_heatFlow_of_hasFDerivAt a t f q hd x).unique
      (hasFDerivAt_heatFlow ha ht f x)
  rw [heq]
  exact norm_heatFDerivBUC_le ha ht f

/-- Smoothing applied to an existing second derivative. -/
theorem norm_heatFlow_second_fderivative_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC E F) (q : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hd : ∀ x, HasFDerivAt f (q x) x) (hd' : ∀ x, HasFDerivAt q (h x) x) :
    ‖heatFlowBUC a t h‖ ≤ ‖f‖ / (a * t) := by
  have heq : heatFlowBUC a t q = heatFDerivBUC ha ht f := by
    ext x : 1
    exact (hasFDerivAt_heatFlow_of_hasFDerivAt a t f q hd x).unique
      (hasFDerivAt_heatFlow ha ht f x)
  have heq' : heatFlowBUC a t h = heatSecondFDerivBUC ha ht f := by
    ext x : 1
    have hdq : HasFDerivAt (heatFlowBUC a t q) (heatFlowBUC a t h x) x :=
      hasFDerivAt_heatFlow_of_hasFDerivAt a t q h hd' x
    rw [heq] at hdq
    exact hdq.unique (hasFDerivAt_heatFDerivBUC ha ht f x)
  rw [heq']
  exact norm_heatSecondFDerivBUC_le ha ht f

/-- The first-derivative estimate with the nonsingular `(1+t)^(-1/2)` weight. -/
theorem norm_heatFlow_fderivative_decay_le {a t M : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (f : BUC E F) (q : BUC E (E →L[ℝ] F))
    (hd : ∀ x, HasFDerivAt f (q x) x) (hf : ‖f‖ ≤ M) (hq : ‖q‖ ≤ M) :
    ‖heatFlowBUC a t q‖ ≤
      ((2 : ℝ) ^ (1 / 2 : ℝ) * max 1 (Real.sqrt (2 * a))⁻¹) * M *
        (1 + t) ^ (-(1 / 2 : ℝ)) := by
  apply le_one_add_rpow_neg_of_uniform_of_smoothing ((norm_nonneg f).trans hf)
    (by norm_num) ht ((norm_heatFlowBUC_le a t q).trans hq)
  intro htpos
  calc
    _ ≤ ‖f‖ / heatScale a t := norm_heatFlow_fderivative_le ha htpos f q hd
    _ ≤ M / heatScale a t := div_le_div_of_nonneg_right hf (heatScale_pos_of_pos ha htpos).le
    _ = _ := by
      rw [heatScale, Real.sqrt_mul (by positivity : 0 ≤ 2 * a),
        div_eq_mul_inv, mul_inv_rev, Real.rpow_neg ht, ← Real.sqrt_eq_rpow]
      ring

/-- The second-derivative estimate with the nonsingular `(1+t)^(-1)` weight. -/
theorem norm_heatFlow_second_fderivative_decay_le {a t M : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (f : BUC E F) (q : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hd : ∀ x, HasFDerivAt f (q x) x) (hd' : ∀ x, HasFDerivAt q (h x) x)
    (hf : ‖f‖ ≤ M) (hh : ‖h‖ ≤ M) :
    ‖heatFlowBUC a t h‖ ≤ (2 * max 1 a⁻¹) * M * (1 + t) ^ (-(1 : ℝ)) := by
  have hs : 0 < t → ‖heatFlowBUC a t h‖ ≤ a⁻¹ * M * t ^ (-(1 : ℝ)) := by
    intro htpos
    calc
      _ ≤ ‖f‖ / (a * t) := norm_heatFlow_second_fderivative_le ha htpos f q h hd hd'
      _ ≤ M / (a * t) := div_le_div_of_nonneg_right hf (by positivity)
      _ = _ := by rw [Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev]; ring
  simpa only [Real.rpow_one] using le_one_add_rpow_neg_of_uniform_of_smoothing
    ((norm_nonneg f).trans hf) (by norm_num : (0 : ℝ) ≤ 1) ht
    ((norm_heatFlowBUC_le a t h).trans hh) hs

/-- Integrating the first heat derivative preserves the half-power decay. -/
theorem norm_heatDuhamel_fderivative_decay_le {a t M : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (f : ℝ → BUC E F) (q : ℝ → BUC E (E →L[ℝ] F))
    (hd : ∀ r ∈ Icc 0 t, ∀ x, HasFDerivAt (f r) (q r x) x)
    (hf : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4))
    (hq : ∀ r ∈ Icc 0 t, ‖q r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) :
    ‖heatDuhamel a q t‖ ≤ (16 * max 1 (Real.sqrt (2 * a))⁻¹) * M *
      (1 + t) ^ (-(1 / 2 : ℝ)) := by
  have hK : 0 ≤ max 1 (Real.sqrt (2 * a))⁻¹ := le_trans (by norm_num) (le_max_left _ _)
  have hi := norm_integral_le_polynomial_convolution (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)
    (by positivity : 0 ≤ ((2 : ℝ) ^ (1 / 2 : ℝ) * max 1 (Real.sqrt (2 * a))⁻¹) * M)
    ht (fun r ↦ heatFlowBUC a (t - r) (q r)) (by
      intro r hr
      convert! norm_heatFlow_fderivative_decay_le ha (by linarith [hr.2] : 0 ≤ t - r)
        (f r) (q r) (hd r hr) (hf r hr) (hq r hr) using 1
      simp only [add_sub_assoc]
      ring)
  have hpow : (2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  change ‖heatDuhamel a q t‖ ≤ _ at hi
  convert hi using 1
  calc
    _ = (8 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ))) *
        max 1 (Real.sqrt (2 * a))⁻¹ * M * (1 + t) ^ (-(1 / 2 : ℝ)) := by rw [hpow]; ring
    _ = _ := by ring

/-- Integrating the second heat derivative preserves the full-power decay. -/
theorem norm_heatDuhamel_second_fderivative_decay_le {a t M : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (f : ℝ → BUC E F) (q : ℝ → BUC E (E →L[ℝ] F))
    (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] F))
    (hd : ∀ r ∈ Icc 0 t, ∀ x, HasFDerivAt (f r) (q r x) x)
    (hd' : ∀ r ∈ Icc 0 t, ∀ x, HasFDerivAt (q r) (h r x) x)
    (hf : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4))
    (hh : ∀ r ∈ Icc 0 t, ‖h r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) :
    ‖heatDuhamel a h t‖ ≤ (32 * max 1 a⁻¹) * M * (1 + t) ^ (-(1 : ℝ)) := by
  have hK : 0 ≤ max 1 a⁻¹ := le_trans (by norm_num) (le_max_left _ _)
  have hi := norm_integral_le_polynomial_convolution (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 5 / 4) (by positivity : 0 ≤ (2 * max 1 a⁻¹) * M)
    ht (fun r ↦ heatFlowBUC a (t - r) (h r)) (by
      intro r hr
      convert! norm_heatFlow_second_fderivative_decay_le ha (by linarith [hr.2] : 0 ≤ t - r)
        (f r) (q r) (h r) (hd r hr) (hd' r hr) (hf r hr) (hh r hr) using 1
      simp only [add_sub_assoc]
      ring)
  change ‖heatDuhamel a h t‖ ≤ _ at hi
  simpa only [Real.rpow_one, mul_assoc, mul_left_comm, mul_comm,
    show (32 : ℝ) = 8 * 2 * 2 by norm_num] using hi

end

end Planarwave
