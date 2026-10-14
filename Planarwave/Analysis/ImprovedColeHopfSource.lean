/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.IntegrableLogarithmicDecay

@[expose] public section

/-!
# Improved Cole--Hopf source estimates

The improved forcing bound and the uniform `O(M)` Cole--Hopf bound imply
`eq:gxibestest`. Its Duhamel contribution is uniformly quadratic, and the
same is true for the full transformed forcing after the initial pulse.
These are the source estimates in the paper's final phase comparison.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

/-- Absorb the compactly supported initial pulse into the logarithmic
weight when it is multiplied by the small Cole--Hopf variable. -/
theorem trackingCutoff_le_logarithmic_decay {t : ℝ} (ht : 0 ≤ t) :
    trackingCutoff t ≤ (2 * ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2)) *
      ((1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t)) := by
  by_cases hz : trackingCutoff t = 0
  · rw [hz]
    exact mul_nonneg (by positivity)
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith)))
  have ht' := trackingCutoff_ne_zero_mem hz
  have hw := one_add_rpow_neg_le_recent (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (le_refl (0 : ℝ)) ht (by linarith [ht'.2] : t ≤ 0 + 2)
  simp only [add_zero, Real.one_rpow] at hw
  have hlog : (1 : ℝ) / 2 ≤ Real.log (2 + t) := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono : Real.log 2 ≤ Real.log (2 + t) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at htwo
    linarith
  have hprod := mul_le_mul hw hlog (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _))
  calc
    _ ≤ ‖trackingCutoff‖ := trackingCutoff_le_norm t
    _ ≤ ‖trackingCutoff‖ * (2 * ((3 : ℝ) ^ ((3 : ℝ) / 2) *
        (1 + t) ^ (-((3 : ℝ) / 2)) * Real.log (2 + t))) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith : 1 ≤
        2 * ((3 : ℝ) ^ ((3 : ℝ) / 2) * (1 + t) ^ (-((3 : ℝ) / 2)) * Real.log (2 + t))) (norm_nonneg trackingCutoff)
    _ = _ := by rw [neg_div]; ring

section Product

variable {E : Type*} [PseudoMetricSpace E]

/-- Equation `eq:gxibestest`, including the initial forcing pulse. -/
theorem norm_coleHopf_forcing_product_improved_le (g ξ : BUC E ℝ) {K G M t : ℝ}
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hM : 0 ≤ M) (hM1 : M ≤ 1) (ht : 0 ≤ t)
    (hξ : ‖ξ‖ ≤ K * M)
    (hg : ‖g‖ ≤ G * (trackingCutoff t * M + M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t))) :
    ‖BUC.smulBUC g ξ‖ ≤
      (G * K * (2 * ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2) + 1)) *
        M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) := by
  let w := (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t)
  let J := 2 * ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2)
  have hw : 0 ≤ w := mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith))
  have hρ : trackingCutoff t ≤ J * w := trackingCutoff_le_logarithmic_decay ht
  have hsquare : M ^ 2 ≤ M := by nlinarith
  calc
    _ ≤ ‖g‖ * ‖ξ‖ := BUC.norm_smulBUC_le g ξ
    _ ≤ (G * (trackingCutoff t * M + M ^ 2 * w)) * (K * M) :=
      mul_le_mul (by simpa only [w, mul_assoc] using hg) hξ (norm_nonneg _)
        ((norm_nonneg g).trans (by simpa only [w, mul_assoc] using hg))
    _ ≤ (G * ((J * w) * M + M * w)) * (K * M) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hK hM)
      apply mul_le_mul_of_nonneg_left _ hG
      exact add_le_add (mul_le_mul_of_nonneg_right hρ hM) (mul_le_mul_of_nonneg_right hsquare hw)
    _ = _ := by dsimp only [J, w]; ring

end Product

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The product term in the comparison equation has uniformly quadratic
Duhamel size, independently of the time horizon. -/
theorem norm_heatDuhamel_coleHopf_product_improved_le (a : ℝ) (g ξ : ℝ → BUC E ℝ)
    {K G M t : ℝ} (hK : 0 ≤ K) (hG : 0 ≤ G) (hM : 0 ≤ M) (hM1 : M ≤ 1) (ht : 0 ≤ t)
    (hξ : ∀ r ∈ Icc 0 t, ‖ξ r‖ ≤ K * M)
    (hg : ∀ r ∈ Icc 0 t, ‖g r‖ ≤ G *
      (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) :
    ‖heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (ξ r)) t‖ ≤
      32 * (G * K * (2 * ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2) + 1)) * M ^ 2 := by
  have h := norm_heat_integral_le_logarithmic_decay a (fun r ↦ BUC.smulBUC (g r) (ξ r))
    (le_refl (0 : ℝ)) ht
    (show 0 ≤ (G * K * (2 * ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2) + 1)) * M ^ 2 by positivity)
    (fun r hr ↦ norm_coleHopf_forcing_product_improved_le (g r) (ξ r) hK hG hM hM1 hr.1 (hξ r hr) (hg r hr))
  simpa only [heatDuhamel, mul_assoc] using h

/-- After the first unit interval there is no initial pulse. The full
forcing of the Cole--Hopf comparison then has quadratic time mass. -/
theorem norm_heat_integral_forcedColeHopfSource_after_one_le (a β : ℝ) (g ξ : ℝ → BUC E ℝ)
    {K G M s t : ℝ} (hK : 0 ≤ K) (hG : 0 ≤ G) (hM1 : M ≤ 1)
    (hs : 1 ≤ s) (hst : s ≤ t) (hξ : ∀ r ∈ Icc s t, ‖ξ r‖ ≤ K * M)
    (hg : ∀ r ∈ Icc s t, ‖g r‖ ≤ G *
      (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) :
    ‖∫ r in s..t, heatFlowBUC a (t - r) (forcedColeHopfSource β (g r) (ξ r))‖ ≤
      32 * (G * (1 + |β| * K)) * M ^ 2 := by
  have h := norm_heat_integral_le_logarithmic_decay a (fun r ↦ forcedColeHopfSource β (g r) (ξ r))
    (by linarith : 0 ≤ s) hst
    (show 0 ≤ (G * (1 + |β| * K)) * M ^ 2 by positivity) ?_
  · simpa only [mul_assoc] using h
  intro r hr
  have hξ' : ‖ξ r‖ ≤ K := (hξ r hr).trans (by nlinarith)
  have hg' := hg r hr
  rw [trackingCutoff_eq_zero_of_ge (by linarith [hr.1] : (3 : ℝ) / 4 ≤ r), zero_mul, zero_add] at hg'
  calc
    _ ≤ ‖g r‖ * (1 + |β| * ‖ξ r‖) := norm_forcedColeHopfSource_le β (g r) (ξ r)
    _ ≤ (G * (M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) * (1 + |β| * K) :=
      mul_le_mul hg' (by gcongr) (by positivity) ((norm_nonneg (g r)).trans hg')
    _ = _ := by ring

end

end Planarwave
