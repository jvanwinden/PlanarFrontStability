/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCNonlinear
public import Planarwave.Analysis.DelayedHeatForcingCancellation
public import Planarwave.Analysis.IntegralGronwall
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

/-!
# Supremum bounds for the forced Cole--Hopf equation

This is the zero-order a priori estimate in Lemma `lem:xiAP`. Heat
contractivity and integral Grönwall give a bound depending only on the
total forcing mass. The paper's `(1+t)^(-5/4)` assumption therefore gives
a bound uniform in the final time. `IsForcedColeHopfMild` records a mild
solution, and does not postulate that one exists. Existence is proved
separately in `ForcedColeHopfExistence`; higher regularity is not asserted
by the estimates here.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

section Source

variable {E : Type*} [PseudoMetricSpace E]

/-- The source `g (1 + β ξ)` in the transformed equation. -/
def forcedColeHopfSource (β : ℝ) (g ξ : BUC E ℝ) : BUC E ℝ :=
  g + β • BUC.smulBUC g ξ

@[simp]
theorem forcedColeHopfSource_apply (β : ℝ) (g ξ : BUC E ℝ) (x : E) :
    forcedColeHopfSource β g ξ x = g x * (1 + β * ξ x) := by
  simp [forcedColeHopfSource, smul_eq_mul]; ring

theorem norm_forcedColeHopfSource_le (β : ℝ) (g ξ : BUC E ℝ) :
    ‖forcedColeHopfSource β g ξ‖ ≤ ‖g‖ * (1 + |β| * ‖ξ‖) := by
  calc
    _ ≤ ‖g‖ + ‖β • BUC.smulBUC g ξ‖ := norm_add_le _ _
    _ ≤ ‖g‖ + |β| * (‖g‖ * ‖ξ‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact BUC.norm_smulBUC_le g ξ
    _ = _ := by ring

theorem forcedColeHopfSource_sub (β : ℝ) (g ξ η : BUC E ℝ) :
    forcedColeHopfSource β g ξ - forcedColeHopfSource β g η =
      β • BUC.smulBUC g (ξ - η) := by
  ext x
  simp [smul_eq_mul]
  ring

theorem norm_forcedColeHopfSource_sub_le (β : ℝ) (g ξ η : BUC E ℝ) :
    ‖forcedColeHopfSource β g ξ - forcedColeHopfSource β g η‖ ≤
      |β| * ‖g‖ * ‖ξ - η‖ := by
  rw [forcedColeHopfSource_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (BUC.norm_smulBUC_le g (ξ - η)) (abs_nonneg β)

theorem continuous_forcedColeHopfSource (β : ℝ) :
    Continuous (fun p : BUC E ℝ × BUC E ℝ ↦ forcedColeHopfSource β p.1 p.2) := by
  exact continuous_fst.add
    ((BUC.continuous_bilinearBUC (ContinuousLinearMap.lsmul ℝ ℝ)).const_smul β)

end Source

/-- Exact accumulated mass of the integrable time weight in Lemma `lem:xiAP`. -/
theorem integral_one_add_rpow_neg_five_quarters {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, (1 + r) ^ (-(5 : ℝ) / 4)) =
      4 * (1 - (1 + t) ^ (-(1 : ℝ) / 4)) := by
  have hc : ContinuousOn (fun r : ℝ ↦ (1 + r) ^ (-(5 : ℝ) / 4)) (Icc 0 t) :=
    (continuousOn_const.add continuousOn_id).rpow_const
      (fun r hr ↦ Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))
  have hd : ∀ r ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ ↦ -4 * (1 + s) ^ (-(1 : ℝ) / 4))
        ((1 + r) ^ (-(5 : ℝ) / 4)) r := by
    intro r hr
    rw [uIcc_of_le ht] at hr
    have h := (((hasDerivAt_id r).const_add 1).rpow_const
      (p := -(1 : ℝ) / 4) (Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))).const_mul (-4)
    convert! h using 1
    norm_num
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc ht)
  simpa only [add_zero, Real.one_rpow] using h.trans (by ring)

/-- The forcing weight has time mass at most four, independently of `t`. -/
theorem integral_one_add_rpow_neg_five_quarters_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, (1 + r) ^ (-(5 : ℝ) / 4)) ≤ 4 := by
  rw [integral_one_add_rpow_neg_five_quarters ht]
  nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ 1 + t) (-(1 : ℝ) / 4)]

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The zero-initial-data Duhamel equation from `eq:xiduhamellem`. -/
structure IsForcedColeHopfMild (a β : ℝ) (g ξ : ℝ → BUC E ℝ) (T : ℝ) : Prop where
  continuous : ContinuousOn ξ (Icc 0 T)
  duhamel : ∀ t ∈ Icc 0 T,
    ξ t = -heatDuhamel a (fun r ↦ forcedColeHopfSource β (g r) (ξ r)) t

/-- Heat contractivity gives precisely the integral inequality used before
Grönwall in the paper. -/
theorem IsForcedColeHopfMild.norm_le_integral {a β T : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hg : ContinuousOn g (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖ξ t‖ ≤ ∫ r in (0 : ℝ)..t, ‖g r‖ * (1 + |β| * ‖ξ r‖) := by
  rw [hξ.duhamel t ht, norm_neg, heatDuhamel]
  apply intervalIntegral.norm_integral_le_of_norm_le ht.1
  · filter_upwards [] with r hr
    exact (norm_heatFlowBUC_le _ _ _).trans (norm_forcedColeHopfSource_le β (g r) (ξ r))
  · exact ((hg.norm.mul (continuousOn_const.add (hξ.continuous.norm.const_mul |β|))).mono
      (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-- The supremum estimate depends on the forcing's total time mass, not on
the time interval's length. -/
theorem IsForcedColeHopfMild.norm_le_of_integral_norm_le
    {a β T B : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hg : ContinuousOn g (Icc 0 T))
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hmass : ∀ t ∈ Icc 0 T, (∫ r in (0 : ℝ)..t, ‖g r‖) ≤ B)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖ξ t‖ ≤ B * Real.exp (|β| * B) := by
  have hi : ∀ s ∈ Icc 0 T,
      ‖ξ s‖ ≤ B + ∫ r in (0 : ℝ)..s, (|β| * ‖g r‖) * ‖ξ r‖ := by
    intro s hs
    have h1 := (hg.norm.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc
      (μ := volume) hs.1
    have h2 : IntervalIntegrable (fun r ↦ (|β| * ‖g r‖) * ‖ξ r‖) volume 0 s := by
      exact (((hg.norm.const_mul |β|).mul hξ.continuous.norm).mono
        (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    calc
      ‖ξ s‖ ≤ ∫ r in (0 : ℝ)..s, ‖g r‖ * (1 + |β| * ‖ξ r‖) :=
        hξ.norm_le_integral hg hs
      _ = (∫ r in (0 : ℝ)..s, ‖g r‖) +
          ∫ r in (0 : ℝ)..s, (|β| * ‖g r‖) * ‖ξ r‖ := by
        rw [← intervalIntegral.integral_add h1 h2]
        congr 1
        funext r
        ring
      _ ≤ _ := add_le_add (hmass s hs) (le_refl _)
  apply (le_exp_integral_of_le_add_integral_mul hT hξ.continuous.norm
    (hg.norm.const_mul |β|) (fun s _ ↦ mul_nonneg (abs_nonneg β) (norm_nonneg (g s)))
    hi t ht).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.exp_le_exp.mpr
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hmass t ht) (abs_nonneg β)

/-- Specialization of the mass bound to the paper's integrable decay rate.
The explicit coefficient is independent of `T` and of `M ∈ [0,1]`. -/
theorem IsForcedColeHopfMild.norm_le_of_decay
    {a β T C M : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hg : ContinuousOn g (Icc 0 T))
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hdecay : ∀ t ∈ Icc 0 T, ‖g t‖ ≤ C * M * (1 + t) ^ (-(5 : ℝ) / 4))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖ξ t‖ ≤ (4 * C * Real.exp (4 * |β| * C)) * M := by
  have hmass : ∀ s ∈ Icc 0 T, (∫ r in (0 : ℝ)..s, ‖g r‖) ≤ 4 * C * M := by
    intro s hs
    have hw : ContinuousOn (fun r : ℝ ↦ (1 + r) ^ (-(5 : ℝ) / 4)) (Icc 0 s) :=
      (continuousOn_const.add continuousOn_id).rpow_const
        (fun r hr ↦ Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))
    calc
      _ ≤ ∫ r in (0 : ℝ)..s, C * M * (1 + r) ^ (-(5 : ℝ) / 4) :=
        intervalIntegral.integral_mono_on hs.1
          ((hg.norm.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1)
          ((hw.const_mul (C * M)).intervalIntegrable_of_Icc hs.1)
          (fun r hr ↦ hdecay r ⟨hr.1, hr.2.trans hs.2⟩)
      _ = (C * M) * ∫ r in (0 : ℝ)..s, (1 + r) ^ (-(5 : ℝ) / 4) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (C * M) * 4 := mul_le_mul_of_nonneg_left
        (integral_one_add_rpow_neg_five_quarters_le hs.1) (mul_nonneg hC hM)
      _ = _ := by ring
  calc
    ‖ξ t‖ ≤ (4 * C * M) * Real.exp (|β| * (4 * C * M)) :=
      hξ.norm_le_of_integral_norm_le hg hT (by positivity) hmass ht
    _ ≤ (4 * C * M) * Real.exp (4 * |β| * C) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      calc
        |β| * (4 * C * M) = (4 * |β| * C) * M := by ring
        _ ≤ (4 * |β| * C) * 1 := mul_le_mul_of_nonneg_left hM1 (by positivity)
        _ = _ := mul_one _
    _ = _ := by ring

/-- Zero initial data is a consequence of the Duhamel equation. -/
theorem IsForcedColeHopfMild.initial {a β T : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hT : 0 ≤ T) : ξ 0 = 0 := by
  simpa [heatDuhamel] using hξ.duhamel 0 ⟨le_refl 0, hT⟩

/-- Uniqueness in the continuous BUC mild-solution class, with no smallness
assumption on the forcing or on the length of the interval. -/
theorem IsForcedColeHopfMild.unique {a β T : ℝ} {g ξ η : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hη : IsForcedColeHopfMild a β g η T)
    (hg : ContinuousOn g (Icc 0 T)) (hT : 0 ≤ T) : EqOn ξ η (Icc 0 T) := by
  have hi : ∀ t ∈ Icc 0 T,
      ‖ξ t - η t‖ ≤ 0 + ∫ r in (0 : ℝ)..t, (|β| * ‖g r‖) * ‖ξ r - η r‖ := by
    intro t ht
    have hcξ := (continuous_forcedColeHopfSource β).comp_continuousOn (hg.prodMk hξ.continuous)
    have hcη := (continuous_forcedColeHopfSource β).comp_continuousOn (hg.prodMk hη.continuous)
    have hiξ : IntervalIntegrable
        (fun r ↦ heatFlowBUC a (t - r) (forcedColeHopfSource β (g r) (ξ r))) volume 0 t :=
      (((continuous_heatFlowBUC_joint a).comp_continuousOn
        ((continuousOn_const.sub continuousOn_id).prodMk hcξ)).mono
        (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hiη : IntervalIntegrable
        (fun r ↦ heatFlowBUC a (t - r) (forcedColeHopfSource β (g r) (η r))) volume 0 t :=
      (((continuous_heatFlowBUC_joint a).comp_continuousOn
        ((continuousOn_const.sub continuousOn_id).prodMk hcη)).mono
        (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    rw [hξ.duhamel t ht, hη.duhamel t ht, neg_sub_neg, norm_sub_rev,
      heatDuhamel, heatDuhamel, ← intervalIntegral.integral_sub hiξ hiη, zero_add]
    apply intervalIntegral.norm_integral_le_of_norm_le ht.1
    · filter_upwards [] with r hr
      change ‖(heatOperator a (t - r)) (forcedColeHopfSource β (g r) (ξ r)) -
        (heatOperator a (t - r)) (forcedColeHopfSource β (g r) (η r))‖ ≤ _
      rw [← map_sub]
      exact (norm_heatFlowBUC_le _ _ _).trans (norm_forcedColeHopfSource_sub_le β (g r) (ξ r) (η r))
    · exact ((((hg.norm.const_mul |β|).mul (hξ.continuous.sub hη.continuous).norm)).mono
        (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  intro t ht
  have h := le_exp_integral_of_le_add_integral_mul hT
    (hξ.continuous.sub hη.continuous).norm (hg.norm.const_mul |β|)
    (fun r _ ↦ mul_nonneg (abs_nonneg β) (norm_nonneg (g r))) hi t ht
  simpa only [Pi.sub_apply, zero_mul, norm_le_zero_iff, sub_eq_zero] using! h

end

end Planarwave
