/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfBounds
public import Planarwave.Analysis.BUCBilinear

@[expose] public section

/-!
# Grönwall bounds for bilinear heat equations

The C^k argument of `lem:xiAP` uses heat contractivity and a bounded
product rule. This version works in any Banach-valued BUC space, so it
also applies to genuine derivative jets, with their product-rule constant.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Heat contractivity and a bounded bilinear product give the integral
inequality before Grönwall, with the product-rule constant explicit. -/
theorem norm_le_integral_of_bilinear_heatDuhamel {a β T K : ℝ}
    (B : F →L[ℝ] F →L[ℝ] F) (_hK : 0 ≤ K) (hB : ‖B‖ ≤ K)
    {g u : ℝ → BUC E F} (hg : ContinuousOn g (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T))
    (heq : ∀ t ∈ Icc 0 T, u t = -heatDuhamel a
      (fun r ↦ g r + β • BUC.bilinearBUC B (g r) (u r)) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ≤ ∫ r in (0 : ℝ)..t, ‖g r‖ * (1 + (|β| * K) * ‖u r‖) := by
  rw [heq t ht, norm_neg, heatDuhamel]
  apply intervalIntegral.norm_integral_le_of_norm_le ht.1
  · filter_upwards [] with r _
    apply (norm_heatFlowBUC_le _ _ _).trans
    calc
      _ ≤ ‖g r‖ + ‖β • BUC.bilinearBUC B (g r) (u r)‖ := norm_add_le _ _
      _ ≤ ‖g r‖ + |β| * (K * ‖g r‖ * ‖u r‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact (BUC.norm_bilinearBUC_le B (g r) (u r)).trans (by gcongr)
      _ = _ := by ring
  · exact ((hg.norm.mul (continuousOn_const.add (hu.norm.const_mul (|β| * K)))).mono
      (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-- The bound depends on the accumulated forcing mass, not on the
length of the interval. -/
theorem norm_le_mass_of_bilinear_heatDuhamel {a β T K A : ℝ}
    (B : F →L[ℝ] F →L[ℝ] F) (hK : 0 ≤ K) (hB : ‖B‖ ≤ K)
    {g u : ℝ → BUC E F} (hg : ContinuousOn g (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T)) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (heq : ∀ t ∈ Icc 0 T, u t = -heatDuhamel a
      (fun r ↦ g r + β • BUC.bilinearBUC B (g r) (u r)) t)
    (hmass : ∀ t ∈ Icc 0 T, (∫ r in (0 : ℝ)..t, ‖g r‖) ≤ A)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ≤ A * Real.exp ((|β| * K) * A) := by
  have hi : ∀ s ∈ Icc 0 T,
      ‖u s‖ ≤ A + ∫ r in (0 : ℝ)..s, ((|β| * K) * ‖g r‖) * ‖u r‖ := by
    intro s hs
    have h1 := (hg.norm.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc
      (μ := volume) hs.1
    have h2 : IntervalIntegrable (fun r ↦ ((|β| * K) * ‖g r‖) * ‖u r‖) volume 0 s :=
      ((((hg.norm.const_mul (|β| * K)).mul hu.norm)).mono
        (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    calc
      ‖u s‖ ≤ ∫ r in (0 : ℝ)..s, ‖g r‖ * (1 + (|β| * K) * ‖u r‖) :=
        norm_le_integral_of_bilinear_heatDuhamel B hK hB hg hu heq hs
      _ = (∫ r in (0 : ℝ)..s, ‖g r‖) +
          ∫ r in (0 : ℝ)..s, ((|β| * K) * ‖g r‖) * ‖u r‖ := by
        rw [← intervalIntegral.integral_add h1 h2]
        congr 1
        funext r
        ring
      _ ≤ _ := add_le_add (hmass s hs) le_rfl
  apply (le_exp_integral_of_le_add_integral_mul hT hu.norm
    (hg.norm.const_mul (|β| * K)) (fun r _ ↦ by positivity) hi t ht).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hmass t ht) (mul_nonneg (abs_nonneg β) hK)

/-- The integrable forcing rate of the paper gives a bound linear in
`M`, uniform over all final times and all `M ∈ [0,1]`. -/
theorem norm_le_decay_of_bilinear_heatDuhamel {a β T K C M : ℝ}
    (B : F →L[ℝ] F →L[ℝ] F) (hK : 0 ≤ K) (hB : ‖B‖ ≤ K)
    {g u : ℝ → BUC E F} (hg : ContinuousOn g (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T)) (hT : 0 ≤ T)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (heq : ∀ t ∈ Icc 0 T, u t = -heatDuhamel a
      (fun r ↦ g r + β • BUC.bilinearBUC B (g r) (u r)) t)
    (hdecay : ∀ t ∈ Icc 0 T, ‖g t‖ ≤ C * M * (1 + t) ^ (-(5 : ℝ) / 4))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ≤ (4 * C * Real.exp (4 * |β| * K * C)) * M := by
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
    ‖u t‖ ≤ (4 * C * M) * Real.exp ((|β| * K) * (4 * C * M)) :=
      norm_le_mass_of_bilinear_heatDuhamel B hK hB hg hu hT (by positivity) heq hmass ht
    _ ≤ (4 * C * M) * Real.exp (4 * |β| * K * C) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      calc
        (|β| * K) * (4 * C * M) = (4 * |β| * K * C) * M := by ring
        _ ≤ (4 * |β| * K * C) * 1 := mul_le_mul_of_nonneg_left hM1 (by positivity)
        _ = _ := mul_one _
    _ = _ := by ring

end

end Planarwave
