/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.TemporalCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Polynomial weights on the delayed tracking blocks

The source for a forcing pulse is at most two time units old. Comparing
`1 + t` with `3 * (1 + r)` transfers any nonnegative polynomial decay
exponent to the current time. These scalar facts are used both for the
forcing estimate and for the fully cancelled critical component.
-/

open Set

namespace Planarwave

/-- A polynomial decay weight is decreasing on nonnegative times. -/
theorem one_add_rpow_neg_antitone {p s t : ℝ} (hp : 0 ≤ p) (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 + t) ^ (-p) ≤ (1 + s) ^ (-p) :=
  Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hp)

/-- The weight changes by at most `3^p` over the last two time units. -/
theorem one_add_rpow_neg_le_recent {p s t : ℝ} (hp : 0 ≤ p) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hts : t ≤ s + 2) : (1 + s) ^ (-p) ≤ (3 : ℝ) ^ p * (1 + t) ^ (-p) := by
  have hbase : 1 + t ≤ 3 * (1 + s) := by linarith
  calc
    (1 + s) ^ (-p) = (3 : ℝ) ^ p * (3 * (1 + s)) ^ (-p) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by linarith : 0 ≤ 1 + s),
        ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), add_neg_cancel,
        Real.rpow_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) hbase (neg_nonpos.mpr hp))
      (Real.rpow_nonneg (by norm_num) p)

/-- Every time after the first unit interval belongs to a delayed block,
including integer endpoints. -/
theorem exists_delayed_time_block {t : ℝ} (ht : 1 ≤ t) :
    ∃ (n : ℕ) (τ : ℝ), τ ∈ Icc (0 : ℝ) 1 ∧ t = (n : ℝ) + 1 + τ := by
  refine ⟨⌊t - 1⌋₊, t - 1 - (⌊t - 1⌋₊ : ℝ), ⟨?_, ?_⟩, ?_⟩
  · exact sub_nonneg.mpr (Nat.floor_le (by linarith))
  · have h := Nat.lt_floor_add_one (t - 1)
    linarith
  · ring

/-- Convert an initial bound and completed-block bounds to one uniform
polynomial decay estimate. No continuity of the scalar quantity is needed. -/
theorem le_decay_of_delayed_block_bounds {u : ℝ → ℝ} {p R A T : ℝ}
    (hp : 0 ≤ p) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hi : ∀ t ∈ Icc 0 T, t ≤ 1 → u t ≤ R * A)
    (hb : ∀ (n : ℕ) (τ : ℝ), τ ∈ Icc (0 : ℝ) 1 → (n : ℝ) + 1 + τ ≤ T →
      u ((n : ℝ) + 1 + τ) ≤ R * (A * (1 + (n : ℝ)) ^ (-p)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : u t ≤ (R * (3 : ℝ) ^ p) * A * (1 + t) ^ (-p) := by
  by_cases ht1 : t ≤ 1
  · have hw := one_add_rpow_neg_le_recent hp (le_refl (0 : ℝ)) ht.1 (by linarith : t ≤ 0 + 2)
    simp only [add_zero, Real.one_rpow] at hw
    calc
      u t ≤ R * A := hi t ht ht1
      _ ≤ (R * A) * ((3 : ℝ) ^ p * (1 + t) ^ (-p)) :=
        (mul_one (R * A)).symm.le.trans (mul_le_mul_of_nonneg_left hw (mul_nonneg hR hA))
      _ = _ := by ring
  · obtain ⟨n, τ, hτ, rfl⟩ := exists_delayed_time_block (le_of_lt (lt_of_not_ge ht1))
    calc
      _ ≤ R * (A * (1 + (n : ℝ)) ^ (-p)) := hb n τ hτ ht.2
      _ ≤ R * (A * ((3 : ℝ) ^ p * (1 + ((n : ℝ) + 1 + τ)) ^ (-p))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (one_add_rpow_neg_le_recent hp (Nat.cast_nonneg n) ht.1 (by linarith [hτ.2])) hA) hR
      _ = _ := by ring

end Planarwave
