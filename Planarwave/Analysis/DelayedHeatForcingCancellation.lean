/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamel

@[expose] public section

/-!
# Cancellation of completed forcing pulses

The semigroup law and the cutoff's unit integral are the mechanism behind
Step 3b of the nonlinear iteration. The initial pulse exactly cancels the
critical initial heat orbit. Each completed delayed pulse exactly cancels
the critical Duhamel contribution of its preceding source block.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The response to one pulse is its accumulated scalar mass times a single
heat orbit. The zero cutoff handles all negative pulse ages. -/
theorem heatDuhamel_trackingPulse {a b t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (p : BUC E F) :
    heatDuhamel a (fun r ↦ trackingCutoff (r - b) • heatFlowBUC a (r - b) p) t =
      (∫ r in (0 : ℝ)..t, trackingCutoff (r - b)) • heatFlowBUC a (t - b) p := by
  unfold heatDuhamel
  rw [← intervalIntegral.integral_smul_const]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht] at hr
  dsimp only
  rw [heatFlowBUC_smul]
  by_cases hρ : trackingCutoff (r - b) = 0
  · simp only [hρ, zero_smul]
  have hage : 0 ≤ r - b := by linarith [(trackingCutoff_ne_zero_mem hρ).1]
  rw [← heatFlowBUC_add_apply ha (sub_nonneg.mpr hr.2) hage]
  congr 2
  ring

/-- A completed translated pulse has the exact unit response used in the
tracking cancellation, independent of the shape of the smooth cutoff. -/
theorem heatDuhamel_trackingPulse_completed {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : b + 1 ≤ t) (p : BUC E F) :
    heatDuhamel a (fun r ↦ trackingCutoff (r - b) • heatFlowBUC a (r - b) p) t =
      heatFlowBUC a (t - b) p := by
  rw [heatDuhamel_trackingPulse ha (by linarith), integral_trackingCutoff_shift_completed hb ht,
    one_smul]

/-- The initial forcing pulse cancels the entire initial critical heat mode
once the first unit time interval has elapsed. -/
theorem heatDuhamel_initialPulse {a t : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t) (p : BUC E F) :
    heatDuhamel a (fun r ↦ trackingCutoff r • heatFlowBUC a r p) t = heatFlowBUC a t p := by
  simpa only [sub_zero] using
    heatDuhamel_trackingPulse_completed ha (le_refl (0 : ℝ)) (by simpa using ht) p

/-- Propagating a completed source block gives its contribution at the
current time, without introducing an operator-valued integral. -/
theorem heatFlowBUC_delayedHeatBlock_transport {a t : ℝ} (ha : 0 ≤ a)
    (N : ℝ → BUC E F) (k : ℕ) (ht : (k : ℝ) + 1 ≤ t)
    (hN : ContinuousOn N (Icc (k : ℝ) ((k : ℝ) + 1))) :
    heatFlowBUC a (t - ((k : ℝ) + 1)) (delayedHeatBlock a N k) =
      ∫ r in (k : ℝ)..(k : ℝ) + 1, heatFlowBUC a (t - r) (N r) := by
  change (heatOperator a (t - ((k : ℝ) + 1)))
    (∫ r in (k : ℝ)..(k : ℝ) + 1, heatFlowBUC a ((k : ℝ) + 1 - r) (N r)) = _
  rw [← (heatOperator a (t - ((k : ℝ) + 1))).intervalIntegral_comp_comm
    (intervalIntegrable_delayedHeatBlock a N k hN)]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at hr
  change heatFlowBUC a (t - ((k : ℝ) + 1)) (heatFlowBUC a ((k : ℝ) + 1 - r) (N r)) = _
  rw [← heatFlowBUC_add_apply ha (sub_nonneg.mpr ht) (sub_nonneg.mpr hr.2)]
  congr 1
  ring

/-- A fully completed delayed forcing pulse cancels exactly its preceding
nonlinear source block in the critical Duhamel component. -/
theorem heatDuhamel_delayedPulse_completed {a t : ℝ} (ha : 0 ≤ a)
    (N : ℝ → BUC E F) (k : ℕ) (ht : (k : ℝ) + 2 ≤ t)
    (hN : ContinuousOn N (Icc (k : ℝ) ((k : ℝ) + 1))) :
    heatDuhamel a (fun r ↦ trackingCutoff (r - ((k : ℝ) + 1)) •
      heatFlowBUC a (r - ((k : ℝ) + 1)) (delayedHeatBlock a N k)) t =
      ∫ r in (k : ℝ)..(k : ℝ) + 1, heatFlowBUC a (t - r) (N r) := by
  rw [heatDuhamel_trackingPulse_completed ha (by positivity) (by linarith)]
  exact heatFlowBUC_delayedHeatBlock_transport ha N k (by linarith) hN

/-- The Duhamel response of the forcing is the finite sum of its pulse
responses on every bounded time interval. -/
theorem heatDuhamel_delayedHeatForcing_eq_sum (a : ℝ) (p : BUC E F)
    (N : ℝ → BUC E F) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) (hK : t ≤ (K : ℝ) + 1) :
    heatDuhamel a (delayedHeatForcing a p N) t =
      heatDuhamel a (fun r ↦ trackingCutoff r • heatFlowBUC a r p) t +
      ∑ k ∈ Finset.range K, heatDuhamel a (fun r ↦ trackingCutoff (r - ((k : ℝ) + 1)) •
        heatFlowBUC a (r - ((k : ℝ) + 1)) (delayedHeatBlock a N k)) t := by
  let Q := fun (b : ℝ) (q : BUC E F) (r : ℝ) ↦
    heatFlowBUC a (t - r) (trackingCutoff (r - b) • heatFlowBUC a (r - b) q)
  have hQ (b : ℝ) (q : BUC E F) : Continuous (Q b q) :=
    (continuous_heatFlowBUC_joint a).comp ((continuous_const.sub continuous_id).prodMk
      ((trackingCutoff.continuous.comp (continuous_id.sub continuous_const)).smul
        ((continuous_heatFlowBUC_time a q).comp (continuous_id.sub continuous_const))))
  have heq : heatDuhamel a (delayedHeatForcing a p N) t =
      ∫ r in (0 : ℝ)..t, Q 0 p r + ∑ k ∈ Finset.range K, Q ((k : ℝ) + 1) (delayedHeatBlock a N k) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht] at hr
    dsimp only
    change (heatOperator a (t - r)) (delayedHeatForcing a p N r) = _
    rw [delayedHeatForcing_eq_sum a p N K (hr.2.trans hK), map_add, map_sum]
    simp only [Q, sub_zero, heatOperator_apply]
  rw [heq, intervalIntegral.integral_add ((hQ 0 p).intervalIntegrable 0 t)
    ((continuous_finsetSum (Finset.range K) (fun (k : ℕ) _ ↦ hQ ((k : ℝ) + 1) (delayedHeatBlock a N k))).intervalIntegrable 0 t),
    intervalIntegral.integral_finsetSum (fun (k : ℕ) _ ↦ (hQ ((k : ℝ) + 1) (delayedHeatBlock a N k)).intervalIntegrable 0 t)]
  simp only [Q, heatDuhamel, sub_zero]

/-- Equation `eq:T3a`: all completed pulses reproduce the old source
history, leaving only the current pulse partially accumulated. -/
theorem heatDuhamel_delayedHeatForcing_cancel {a : ℝ} (ha : 0 ≤ a)
    (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (0 : ℝ) ((n : ℝ) + 1 + τ))) :
    heatDuhamel a (delayedHeatForcing a p N) ((n : ℝ) + 1 + τ) =
      heatFlowBUC a ((n : ℝ) + 1 + τ) p +
      (∫ r in (0 : ℝ)..(n : ℝ), heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)) +
      (∫ r in (0 : ℝ)..(n : ℝ) + 1 + τ, trackingCutoff (r - ((n : ℝ) + 1))) •
        (∫ r in (n : ℝ)..(n : ℝ) + 1, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ht : 0 ≤ (n : ℝ) + 1 + τ := by linarith [hτ.1]
  have hblock (k : ℕ) (hk : k ≤ n) : ContinuousOn N (Icc (k : ℝ) ((k : ℝ) + 1)) := by
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    exact hN.mono (Icc_subset_Icc (Nat.cast_nonneg k) (by linarith [hτ.1]))
  rw [heatDuhamel_delayedHeatForcing_eq_sum a p N (n + 1) ht
    (by push_cast; linarith [hτ.2]), Finset.sum_range_succ,
    heatDuhamel_initialPulse ha (by linarith [hτ.1])]
  have hsum : (∑ k ∈ Finset.range n, heatDuhamel a
      (fun r ↦ trackingCutoff (r - ((k : ℝ) + 1)) •
        heatFlowBUC a (r - ((k : ℝ) + 1)) (delayedHeatBlock a N k)) ((n : ℝ) + 1 + τ)) =
      ∫ r in (0 : ℝ)..(n : ℝ), heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r) := by
    calc
      _ = ∑ k ∈ Finset.range n, ∫ r in (k : ℝ)..((k + 1 : ℕ) : ℝ),
          heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k < n := Finset.mem_range.mp hk
        have hcast : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
        simpa only [Nat.cast_add, Nat.cast_one] using
          heatDuhamel_delayedPulse_completed ha N k (by linarith [hτ.1]) (hblock k hkn.le)
      _ = _ := by
        have hi : ∀ k < n, IntervalIntegrable
            (fun r ↦ heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
          intro k hk
          have hc := (continuous_heatFlowBUC_joint a).comp_continuousOn
            (((continuousOn_const (c := (n : ℝ) + 1 + τ)).sub continuousOn_id).prodMk (hblock k hk.le))
          dsimp only [Function.comp_def, Pi.sub_apply, id_eq] at hc
          simpa only [Nat.cast_add, Nat.cast_one] using! hc.intervalIntegrable_of_Icc (μ := volume) (by linarith)
        simpa only [Nat.cast_zero] using
          intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ ↦ (k : ℝ)) hi
  rw [hsum, heatDuhamel_trackingPulse ha ht,
    heatFlowBUC_delayedHeatBlock_transport ha N n (by linarith [hτ.1]) (hblock n le_rfl)]
  abel

/-- The fully cancelled critical expression depends on at most the last
two time blocks. This is the formula used to estimate `ζ` in Step 3b. -/
theorem heatCriticalResidual_eq_recent {a : ℝ} (ha : 0 ≤ a)
    (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (0 : ℝ) ((n : ℝ) + 1 + τ))) :
    heatFlowBUC a ((n : ℝ) + 1 + τ) p + heatDuhamel a N ((n : ℝ) + 1 + τ) -
      heatDuhamel a (delayedHeatForcing a p N) ((n : ℝ) + 1 + τ) =
      (∫ r in (n : ℝ)..(n : ℝ) + 1 + τ, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)) -
      (∫ r in (0 : ℝ)..(n : ℝ) + 1 + τ, trackingCutoff (r - ((n : ℝ) + 1))) •
        (∫ r in (n : ℝ)..(n : ℝ) + 1, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)) := by
  have ht : 0 ≤ (n : ℝ) + 1 + τ := by have := Nat.cast_nonneg (α := ℝ) n; linarith [hτ.1]
  have hc := (continuous_heatFlowBUC_joint a).comp_continuousOn
    (((continuousOn_const (c := (n : ℝ) + 1 + τ)).sub continuousOn_id).prodMk hN)
  dsimp only [Function.comp_def, Pi.sub_apply, id_eq] at hc
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) ht
  have hin := (hc.mono (Icc_subset_Icc le_rfl (by linarith [hτ.1]))).intervalIntegrable_of_Icc (μ := volume)
    (Nat.cast_nonneg (α := ℝ) n)
  have hsplit := intervalIntegral.integral_interval_sub_left hi hin
  rw [heatDuhamel_delayedHeatForcing_cancel ha p N n hτ hN]
  dsimp only [heatDuhamel]
  rw [← hsplit]
  abel

/-- The cancellation bounds the critical residual solely by the source on
its last two blocks, independently of all earlier history and initial data. -/
theorem norm_heatCriticalResidual_le {a : ℝ} (ha : 0 ≤ a)
    (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (0 : ℝ) ((n : ℝ) + 1 + τ)))
    (hM : 0 ≤ M) (hbound : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1 + τ), ‖N r‖ ≤ M) :
    ‖heatFlowBUC a ((n : ℝ) + 1 + τ) p + heatDuhamel a N ((n : ℝ) + 1 + τ) -
      heatDuhamel a (delayedHeatForcing a p N) ((n : ℝ) + 1 + τ)‖ ≤ 3 * M := by
  have ht : 0 ≤ (n : ℝ) + 1 + τ := by have := Nat.cast_nonneg (α := ℝ) n; linarith [hτ.1]
  have hmass := integral_trackingCutoff_shift_mem (b := (n : ℝ) + 1) ht
  have hb (b : ℝ) (hnb : (n : ℝ) ≤ b) (hbt : b ≤ (n : ℝ) + 1 + τ) :
      ‖∫ r in (n : ℝ)..b, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ ≤ M * (b - n) := by
    have hnorm : ∀ r ∈ uIoc (n : ℝ) b,
        ‖heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ ≤ M := by
      intro r hr
      rw [uIoc_of_le hnb] at hr
      exact (norm_heatFlowBUC_le _ _ _).trans (hbound r ⟨hr.1.le, hr.2.trans hbt⟩)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hnb)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  have hfirst := hb ((n : ℝ) + 1 + τ) (by linarith [hτ.1]) le_rfl
  have hsecond : ‖∫ r in (n : ℝ)..(n : ℝ) + 1,
      heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ ≤ M := by
    simpa only [add_sub_cancel_left, mul_one] using hb ((n : ℝ) + 1) (by linarith) (by linarith [hτ.1])
  rw [heatCriticalResidual_eq_recent ha p N n hτ hN]
  calc
    _ ≤ ‖∫ r in (n : ℝ)..(n : ℝ) + 1 + τ, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r)‖ +
        ‖(∫ r in (0 : ℝ)..(n : ℝ) + 1 + τ, trackingCutoff (r - ((n : ℝ) + 1))) •
          (∫ r in (n : ℝ)..(n : ℝ) + 1, heatFlowBUC a ((n : ℝ) + 1 + τ - r) (N r))‖ := norm_sub_le _ _
    _ ≤ M * (((n : ℝ) + 1 + τ) - n) + M := by
      apply add_le_add hfirst
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hmass.1]
      exact (mul_le_mul hmass.2 hsecond (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
    _ ≤ 3 * M := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hτ.2)]

end

end Planarwave
