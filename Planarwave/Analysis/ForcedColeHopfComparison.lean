/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ImprovedColeHopfSource
public import Planarwave.Analysis.ForcedColeHopfPhase

@[expose] public section

/-!
# Comparing the forced and unforced Cole--Hopf variables

This is the final proof's `eq:ictaylor` and `eq:Xfullest`. The initial
forcing pulse cancels the linear Taylor term at time one. Restarting the
comparison equation then gives a uniformly quadratic error at later times.
The mild equation and the improved forcing bound are explicit hypotheses;
this module does not assume the nonlinear tracking construction exists.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

section Taylor

variable {E : Type*} [UniformSpace E]

/-- The first of the initial-data Taylor bounds, in the BUC norm. -/
theorem norm_coleHopfBUC_le_two_mul (β : ℝ) (u : BUC E ℝ)
    (hsmall : |β| * ‖u‖ ≤ 1) : ‖coleHopfBUC β u‖ ≤ 2 * ‖u‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  have hx : |β * u x| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (u.norm_apply_le x) (abs_nonneg β)).trans hsmall
  exact (abs_coleHopf_le_two_mul_abs hx).trans (by gcongr; exact u.norm_apply_le x)

/-- The quadratic Taylor remainder in `eq:ictaylor`. -/
theorem norm_coleHopfBUC_sub_self_le (β : ℝ) (u : BUC E ℝ)
    (hsmall : |β| * ‖u‖ ≤ 1) : ‖coleHopfBUC β u - u‖ ≤ |β| * ‖u‖ ^ 2 := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  have hx : |β * u x| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (u.norm_apply_le x) (abs_nonneg β)).trans hsmall
  calc
    _ ≤ |β| * (u x) ^ 2 := abs_coleHopf_sub_self_le hx
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u x)) (u.norm_apply_le x) 2

end Taylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Linearity of Duhamel only needs continuity on the integration interval. -/
theorem heatDuhamel_add_of_continuousOn (a : ℝ) {f g : ℝ → BUC E ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hf : ContinuousOn f (Icc 0 t)) (hg : ContinuousOn g (Icc 0 t)) :
    heatDuhamel a (fun r ↦ f r + g r) t = heatDuhamel a f t + heatDuhamel a g t := by
  simp only [heatDuhamel, heatFlowBUC_add]
  apply intervalIntegral.integral_add
  · exact ((continuous_heatFlowBUC_joint a).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hf)).intervalIntegrable_of_Icc ht
  · exact ((continuous_heatFlowBUC_joint a).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hg)).intervalIntegrable_of_Icc ht

set_option maxHeartbeats 800000 in
/-- Split the transformed forcing into its linear pulse and product part. -/
theorem heatDuhamel_forcedColeHopfSource (a β : ℝ) {g ξ : ℝ → BUC E ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hg : ContinuousOn g (Icc 0 t)) (hξ : ContinuousOn ξ (Icc 0 t)) :
    heatDuhamel a (fun r ↦ forcedColeHopfSource β (g r) (ξ r)) t =
      heatDuhamel a g t + β • heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (ξ r)) t := by
  have hp : ContinuousOn (fun r ↦ BUC.smulBUC (g r) (ξ r)) (Icc 0 t) :=
    (BUC.continuous_bilinearBUC (ContinuousLinearMap.lsmul ℝ ℝ)).comp_continuousOn
      (hg.prodMk hξ)
  simp only [forcedColeHopfSource]
  calc
    _ = heatDuhamel a g t + heatDuhamel a (fun r ↦ β • BUC.smulBUC (g r) (ξ r)) t := by
      apply heatDuhamel_add_of_continuousOn a ht hg
      exact hp.const_smul β
    _ = _ := by rw [heatDuhamel_smul]

/-- The exact cancellation displayed in the final proof: at time one the
linear initial pulse leaves only the Taylor remainder and the product term. -/
theorem IsForcedColeHopfMild.comparison_at_one {a β T : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (ha : 0 ≤ a) (hT : 1 ≤ T)
    (hg : ContinuousOn g (Icc 0 T)) (p : BUC E ℝ)
    (hpulse : ∀ r ∈ Icc (0 : ℝ) 1, g r = trackingCutoff r • heatFlowBUC a r p) :
    heatFlowBUC a 1 (coleHopfBUC β (-p)) - ξ 1 =
      heatFlowBUC a 1 (coleHopfBUC β (-p) + p) +
        β • heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (ξ r)) 1 := by
  have hg1 : heatDuhamel a g 1 = heatFlowBUC a 1 p :=
    (heatDuhamel_congr a (by norm_num) (fun r hr ↦ hpulse r hr)).trans
      (heatDuhamel_initialPulse ha le_rfl p)
  rw [hξ.duhamel 1 ⟨by norm_num, hT⟩, sub_neg_eq_add,
    heatDuhamel_forcedColeHopfSource a β (by norm_num)
      (hg.mono (Icc_subset_Icc le_rfl hT))
      (hξ.continuous.mono (Icc_subset_Icc le_rfl hT)), hg1, heatFlowBUC_add]
  exact (add_assoc _ _ _).symm

/-- Restart the difference of the unforced heat orbit and forced variable.
This is the second displayed Duhamel identity in the final proof. -/
theorem IsForcedColeHopfMild.comparison_restart {a β T s t : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) (hg : ContinuousOn g (Icc 0 T)) (u : BUC E ℝ) :
    heatFlowBUC a t u - ξ t =
      heatFlowBUC a (t - s) (heatFlowBUC a s u - ξ s) +
        ∫ r in s..t, heatFlowBUC a (t - r) (forcedColeHopfSource β (g r) (ξ r)) := by
  have hc : ContinuousOn (fun r ↦ forcedColeHopfSource β (g r) (ξ r)) (Icc 0 t) :=
    ((continuous_forcedColeHopfSource β).comp_continuousOn
      (hg.prodMk hξ.continuous)).mono (Icc_subset_Icc le_rfl htT)
  rw [hξ.duhamel t ⟨hs.trans hst, htT⟩, hξ.duhamel s ⟨hs, hst.trans htT⟩,
    sub_neg_eq_add, sub_neg_eq_add, heatDuhamel_restart ha hs hst _ hc,
    heatFlowBUC_add, ← heatFlowBUC_add_apply ha (sub_nonneg.mpr hst) hs, sub_add_cancel]
  exact (add_assoc _ _ _).symm

/-- The late-time coefficient consists of the initial Taylor error, the
integrated product source, and the transformed forcing after time one. -/
def coleHopfComparisonQuadraticConstant (β P K G : ℝ) : ℝ :=
  |β| * (P ^ 2 + 32 * (G * K * (2 * ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2) + 1))) +
    32 * (G * (1 + |β| * K))

theorem coleHopfComparisonQuadraticConstant_nonneg (β : ℝ) {P K G : ℝ}
    (hK : 0 ≤ K) (hG : 0 ≤ G) : 0 ≤ coleHopfComparisonQuadraticConstant β P K G := by
  unfold coleHopfComparisonQuadraticConstant
  positivity

/-- The cancellation at one and restart give a quadratic bound uniform
over all later times, as in the proof of `eq:Xfullest`. -/
theorem IsForcedColeHopfMild.norm_comparison_after_one_le
    {a β T P K G M t : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (ha : 0 ≤ a)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (ht : 1 ≤ t) (htT : t ≤ T) (hg : ContinuousOn g (Icc 0 T))
    (p : BUC E ℝ) (hp : ‖p‖ ≤ P * M) (hsmall : |β| * (P * M) ≤ 1)
    (hpulse : ∀ r ∈ Icc (0 : ℝ) 1, g r = trackingCutoff r • heatFlowBUC a r p)
    (hξbound : ∀ r ∈ Icc 0 T, ‖ξ r‖ ≤ K * M)
    (hgbound : ∀ r ∈ Icc 0 T, ‖g r‖ ≤ G *
      (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) :
    ‖heatFlowBUC a t (coleHopfBUC β (-p)) - ξ t‖ ≤
      coleHopfComparisonQuadraticConstant β P K G * M ^ 2 := by
  let B := 32 * (G * K * (2 * ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2) + 1))
  have htaylor : ‖coleHopfBUC β (-p) + p‖ ≤ |β| * P ^ 2 * M ^ 2 := by
    have h := norm_coleHopfBUC_sub_self_le β (-p) (by
      simpa only [norm_neg] using (mul_le_mul_of_nonneg_left hp (abs_nonneg β)).trans hsmall)
    simp only [sub_neg_eq_add, norm_neg] at h
    calc
      _ ≤ |β| * ‖p‖ ^ 2 := h
      _ ≤ |β| * (P * M) ^ 2 := by gcongr
      _ = _ := by ring
  have hproduct : ‖heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (ξ r)) 1‖ ≤ B * M ^ 2 :=
    norm_heatDuhamel_coleHopf_product_improved_le a g ξ hK hG hM hM1 (by norm_num)
      (fun r hr ↦ hξbound r ⟨hr.1, hr.2.trans (ht.trans htT)⟩)
      (fun r hr ↦ hgbound r ⟨hr.1, hr.2.trans (ht.trans htT)⟩)
  have hone : ‖heatFlowBUC a 1 (coleHopfBUC β (-p)) - ξ 1‖ ≤
      (|β| * (P ^ 2 + B)) * M ^ 2 := by
    rw [hξ.comparison_at_one ha (ht.trans htT) hg p hpulse]
    calc
      _ ≤ ‖heatFlowBUC a 1 (coleHopfBUC β (-p) + p)‖ +
          ‖β • heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (ξ r)) 1‖ := norm_add_le _ _
      _ ≤ |β| * P ^ 2 * M ^ 2 + |β| * (B * M ^ 2) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add ((norm_heatFlowBUC_le _ _ _).trans htaylor)
          (mul_le_mul_of_nonneg_left hproduct (abs_nonneg β))
      _ = _ := by ring
  have hlater := norm_heat_integral_forcedColeHopfSource_after_one_le a β g ξ hK hG hM1
    (le_refl (1 : ℝ)) ht
    (fun r hr ↦ hξbound r ⟨by linarith [hr.1], hr.2.trans htT⟩)
    (fun r hr ↦ hgbound r ⟨by linarith [hr.1], hr.2.trans htT⟩)
  rw [hξ.comparison_restart ha (by norm_num : (0 : ℝ) ≤ 1) ht htT hg]
  calc
    _ ≤ ‖heatFlowBUC a (t - 1) (heatFlowBUC a 1 (coleHopfBUC β (-p)) - ξ 1)‖ +
        ‖∫ r in (1 : ℝ)..t, heatFlowBUC a (t - r) (forcedColeHopfSource β (g r) (ξ r))‖ :=
      norm_add_le _ _
    _ ≤ (|β| * (P ^ 2 + B)) * M ^ 2 + 32 * (G * (1 + |β| * K)) * M ^ 2 :=
      add_le_add ((norm_heatFlowBUC_le _ _ _).trans hone) hlater
    _ = _ := by dsimp only [coleHopfComparisonQuadraticConstant, B]; ring

/-- Equation `eq:Xfullest`, with a constant chosen before the time horizon,
the initial perturbation, and the forced solution. -/
theorem exists_forcedColeHopf_comparison_bound (β : ℝ) {P K G : ℝ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C > 0, ∀ {a T M : ℝ} (p : BUC E ℝ) (g ξ : ℝ → BUC E ℝ),
      0 ≤ a → 0 ≤ M → M ≤ 1 → ‖p‖ ≤ P * M → |β| * (P * M) ≤ 1 →
      IsForcedColeHopfMild a β g ξ T → ContinuousOn g (Icc 0 T) →
      (∀ r ∈ Icc 0 (min 1 T), g r = trackingCutoff r • heatFlowBUC a r p) →
      (∀ r ∈ Icc 0 T, ‖ξ r‖ ≤ K * M) →
      (∀ r ∈ Icc 0 T, ‖g r‖ ≤ G *
        (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) →
      ∀ t ∈ Icc 0 T, ‖heatFlowBUC a t (coleHopfBUC β (-p)) - ξ t‖ ≤
        C * (M ^ 2 + M / (1 + t)) := by
  let Q := coleHopfComparisonQuadraticConstant β P K G
  have hQ : 0 ≤ Q := coleHopfComparisonQuadraticConstant_nonneg β hK hG
  let C := 1 + 2 * (2 * P + K) + Q
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a T M p g ξ ha hM hM1 hp hsmall hξ hg hpulse hξbound hgbound t ht
  have hweight : 0 ≤ M / (1 + t) := div_nonneg hM (by linarith [ht.1])
  by_cases ht1 : 1 ≤ t
  · have hlate := hξ.norm_comparison_after_one_le ha hK hG hM hM1 ht1 ht.2 hg p hp hsmall
      (fun r hr ↦ hpulse r ⟨hr.1, le_min hr.2 (hr.2.trans (ht1.trans ht.2))⟩)
      hξbound hgbound
    calc
      _ ≤ Q * M ^ 2 := hlate
      _ ≤ C * (M ^ 2 + M / (1 + t)) := by
        apply mul_le_mul (by dsimp only [C]; linarith) (by linarith) (sq_nonneg M) hC.le
  · have hearly : ‖heatFlowBUC a t (coleHopfBUC β (-p)) - ξ t‖ ≤ (2 * P + K) * M := by
      have hi := norm_coleHopfBUC_le_two_mul β (-p) (by
        simpa only [norm_neg] using (mul_le_mul_of_nonneg_left hp (abs_nonneg β)).trans hsmall)
      calc
        _ ≤ ‖heatFlowBUC a t (coleHopfBUC β (-p))‖ + ‖ξ t‖ := norm_sub_le _ _
        _ ≤ 2 * ‖p‖ + K * M :=
          add_le_add ((norm_heatFlowBUC_le _ _ _).trans (by simpa only [norm_neg] using hi))
            (hξbound t ht)
        _ ≤ (2 * P + K) * M := by nlinarith
    have hhalf : M ≤ 2 * (M / (1 + t)) := by
      have hden : 0 < 1 + t := by linarith [ht.1]
      rw [← mul_div_assoc]
      exact (le_div_iff₀ hden).mpr (by nlinarith)
    calc
      _ ≤ (2 * P + K) * M := hearly
      _ ≤ (2 * (2 * P + K)) * (M / (1 + t)) := by nlinarith
      _ ≤ C * (M ^ 2 + M / (1 + t)) :=
        mul_le_mul (by dsimp only [C]; linarith) (by nlinarith [sq_nonneg M]) hweight hC.le

end

end Planarwave
