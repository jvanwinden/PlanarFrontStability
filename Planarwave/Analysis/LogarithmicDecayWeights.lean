/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedPolynomialDecay
public import Planarwave.Analysis.ForcedPhaseDerivativeDecay

@[expose] public section

/-!
# Logarithmic weights in Step 5 of the nonlinear iteration

Use the low-order phase and tracking bounds in Lemma 4.2. One logarithm
is absorbed by half a power, leaving the integrable `3/2` logarithmic
weight needed for the improved forcing estimate `eq:gbetterest`.
-/

open Set

namespace Planarwave

theorem continuousOn_logarithmic_decay (p T : ℝ) :
    ContinuousOn (fun t : ℝ ↦ (1 + t) ^ (-p) * Real.log (2 + t)) (Icc 0 T) := by
  apply ContinuousOn.mul
  · exact (continuousOn_const.add continuousOn_id).rpow_const
      (fun t ht ↦ Or.inl (by change 1 + t ≠ 0; linarith [ht.1]))
  · exact (continuousOn_const.add continuousOn_id).log
      (fun t ht ↦ by change 2 + t ≠ 0; linarith [ht.1])

/-- Continuity supplies the initial endpoint of a bound proved only for
positive times. This avoids demanding smooth initial perturbations. -/
theorem le_on_Icc_of_le_on_Ioc {f g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (h : ∀ t ∈ Ioc 0 T, f t ≤ g t) : ∀ t ∈ Icc 0 T, f t ≤ g t := by
  have heq : closure (Ioc 0 T) = Icc 0 T := closure_Ioc hT.ne
  simpa only [heq] using le_on_closure h (by rwa [heq]) (by rwa [heq])

theorem log_two_add_le_four_mul_half_rpow {t : ℝ} (ht : 0 ≤ t) :
    Real.log (2 + t) ≤ 4 * (1 + t) ^ (1 / 2 : ℝ) := by
  have hpow : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
  calc
    _ ≤ (2 + t) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
      Real.log_le_rpow_div (by linarith) (by norm_num)
    _ ≤ (2 * (1 + t)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)) (by norm_num)
    _ = (2 * (2 : ℝ) ^ (1 / 2 : ℝ)) * (1 + t) ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1 + t)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)

/-- The tracking weight is bounded by a half-power weight. -/
theorem inverse_mul_log_two_add_le_half_decay {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ (-(1 : ℝ)) * Real.log (2 + t) ≤ 4 * (1 + t) ^ (-(1 / 2 : ℝ)) := by
  calc
    _ ≤ (1 + t) ^ (-(1 : ℝ)) * (4 * (1 + t) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (log_two_add_le_four_mul_half_rpow ht) (Real.rpow_nonneg (by linarith) _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add (by linarith : 0 < 1 + t)]
      norm_num

/-- The logarithmic decay weight changes by a controlled factor on a
completed delayed block; no monotonicity of the entire product is needed. -/
theorem logarithmic_decay_le_recent {p s t : ℝ} (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hst : s ≤ t) (hts : t ≤ s + 2) :
    (1 + s) ^ (-p) * Real.log (2 + s) ≤
      (3 : ℝ) ^ p * ((1 + t) ^ (-p) * Real.log (2 + t)) := by
  calc
    _ ≤ ((3 : ℝ) ^ p * (1 + t) ^ (-p)) * Real.log (2 + t) :=
      mul_le_mul (one_add_rpow_neg_le_recent hp hs (hs.trans hst) hts)
        (Real.log_le_log (by linarith) (by linarith)) (Real.log_nonneg (by linarith))
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _))
    _ = _ := by ring

/-- The scalar power count in the application of Lemma 4.2. -/
theorem projected_nonlinearity_decay_product_le {v l s g K M t : ℝ}
    (hv0 : 0 ≤ v) (hs0 : 0 ≤ s) (hK : 0 ≤ K) (hM : 0 ≤ M) (hM1 : M ≤ 1) (ht : 0 ≤ t)
    (hv : v ≤ K * M * (1 + t) ^ (-(1 : ℝ)) * Real.log (2 + t))
    (hl : l ≤ K * M * (1 + t) ^ (-(1 : ℝ)))
    (hs : s ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)))
    (hg : g ≤ K * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    v * (v + l + s + s ^ 2 + g) ≤
      (K * (7 * K + K ^ 2)) * M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) := by
  have hden : 0 < 1 + t := by linarith
  have hfull : (1 + t) ^ (-(1 : ℝ)) ≤ (1 + t) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hfq : (1 + t) ^ (-(5 : ℝ) / 4) ≤ (1 + t) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hv' : v ≤ (4 * K) * M * (1 + t) ^ (-(1 / 2 : ℝ)) := by
    apply hv.trans
    calc
      _ = (K * M) * ((1 + t) ^ (-(1 : ℝ)) * Real.log (2 + t)) := by ring
      _ ≤ (K * M) * (4 * (1 + t) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (inverse_mul_log_two_add_le_half_decay ht) (mul_nonneg hK hM)
      _ = _ := by ring
  have hl' := hl.trans (mul_le_mul_of_nonneg_left hfull (mul_nonneg hK hM))
  have hg' := hg.trans (mul_le_mul_of_nonneg_left hfq (mul_nonneg hK hM))
  have hs2 := (sq_le_full_decay_of_half_decay hs0 hM hM1 ht hs).trans
    (mul_le_mul_of_nonneg_left hfull (mul_nonneg (sq_nonneg K) hM))
  have hsum : v + l + s + s ^ 2 + g ≤ (7 * K + K ^ 2) * M * (1 + t) ^ (-(1 / 2 : ℝ)) := by
    linarith
  calc
    _ ≤ v * ((7 * K + K ^ 2) * M * (1 + t) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum hv0
    _ ≤ (K * M * (1 + t) ^ (-(1 : ℝ)) * Real.log (2 + t)) *
        ((7 * K + K ^ 2) * M * (1 + t) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right hv (by positivity)
    _ = (K * (7 * K + K ^ 2)) * M ^ 2 *
        ((1 + t) ^ (-(1 : ℝ)) * (1 + t) ^ (-(1 / 2 : ℝ))) * Real.log (2 + t) := by ring
    _ = _ := by rw [← Real.rpow_add hden]; norm_num

end Planarwave
