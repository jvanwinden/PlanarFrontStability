/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.TrackingInterpolation

@[expose] public section

/-!
# Power counting for the nonlinear bootstrap

Substitute the interpolated C² estimate and the low-order phase estimates
into Lemma 4.1, exactly as in Step 5 of `lem:key`.
-/

namespace Planarwave

/-- The quadratic reaction and derivative-dependent terms both gain the
`M^(7/4) (1+t)^(-5/4)` bound needed to improve the source bootstrap. -/
theorem unprojected_nonlinearity_decay_product_le {v V s l g K H M t : ℝ}
    (hv0 : 0 ≤ v) (hV0 : 0 ≤ V) (hs0 : 0 ≤ s) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (ht : 0 ≤ t)
    (hv : v ≤ K * M * (1 + t) ^ (-(1 : ℝ)) * Real.log (2 + t))
    (hV : V ≤ H * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4))
    (hs : s ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)))
    (hl : l ≤ K * M * (1 + t) ^ (-(1 : ℝ)))
    (hg : g ≤ K * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    v ^ 2 + V * (l + s + s ^ 2 + g) ≤
      (36 * K ^ 2 + H * (3 * K + K ^ 2)) * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
  have hden : 0 < 1 + t := by linarith
  have hfull : (1 + t) ^ (-(1 : ℝ)) ≤ (1 + t) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hfq : (1 + t) ^ (-(5 : ℝ) / 4) ≤ (1 + t) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hl' := hl.trans (mul_le_mul_of_nonneg_left hfull (mul_nonneg hK hM))
  have hg' := hg.trans (mul_le_mul_of_nonneg_left hfq (mul_nonneg hK hM))
  have hs2 := (sq_le_full_decay_of_half_decay hs0 hM hM1 ht hs).trans
    (mul_le_mul_of_nonneg_left hfull (mul_nonneg (sq_nonneg K) hM))
  have hsum : l + s + s ^ 2 + g ≤ (3 * K + K ^ 2) * M * (1 + t) ^ (-(1 / 2 : ℝ)) := by
    linarith
  have hproduct : V * (l + s + s ^ 2 + g) ≤
      (H * (3 * K + K ^ 2)) * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
    calc
      _ ≤ V * ((3 * K + K ^ 2) * M * (1 + t) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hV0
      _ ≤ (H * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4)) *
          ((3 * K + K ^ 2) * M * (1 + t) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hV (by positivity)
      _ = (H * (3 * K + K ^ 2)) * (M ^ ((3 : ℝ) / 4) * M) *
          ((1 + t) ^ (-(3 : ℝ) / 4) * (1 + t) ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by
        rw [← Real.rpow_add_one' hM (by norm_num : (3 : ℝ) / 4 + 1 ≠ 0), ← Real.rpow_add hden]
        norm_num
  have hlog : Real.log (2 + t) ≤ 6 * (1 + t) ^ ((3 : ℝ) / 8) := by
    apply (log_two_add_le_small_rpow (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num) ht).trans
    gcongr
    norm_num
  have hv' : v ≤ (6 * K * M) * (1 + t) ^ (-(5 : ℝ) / 8) := by
    calc
      _ ≤ K * M * (1 + t) ^ (-(1 : ℝ)) * Real.log (2 + t) := hv
      _ ≤ K * M * (1 + t) ^ (-(1 : ℝ)) * (6 * (1 + t) ^ ((3 : ℝ) / 8)) := by gcongr
      _ = (6 * K * M) * ((1 + t) ^ (-(1 : ℝ)) * (1 + t) ^ ((3 : ℝ) / 8)) := by ring
      _ = _ := by rw [← Real.rpow_add hden]; norm_num
  have hMpow : M ^ 2 ≤ M ^ ((7 : ℝ) / 4) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge' hM hM1
      (by norm_num : (0 : ℝ) ≤ 7 / 4) (by norm_num : (7 : ℝ) / 4 ≤ 2)
  have htsq : ((1 + t) ^ (-(5 : ℝ) / 8)) ^ 2 = (1 + t) ^ (-(5 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hden.le]
    norm_num
  have hvsq : v ^ 2 ≤ 36 * K ^ 2 * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
    calc
      _ ≤ ((6 * K * M) * (1 + t) ^ (-(5 : ℝ) / 8)) ^ 2 := pow_le_pow_left₀ hv0 hv' 2
      _ = 36 * K ^ 2 * M ^ 2 * (1 + t) ^ (-(5 : ℝ) / 4) := by rw [mul_pow, htsq]; ring
      _ ≤ _ := by gcongr
  nlinarith

end Planarwave
