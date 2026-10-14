/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCNonlinearHigher
public import Planarwave.Analysis.HeatOrbitHigherBounds
public import Planarwave.Analysis.HeatHigherDuhamelSmoothing

@[expose] public section

/-!
# Positive-time regularity of bounded semilinear heat solutions

For scalar diffusion and a smooth vector reaction, iterate one-derivative
Duhamel smoothing on restarted time intervals. The constants depend only
on the reaction, diffusion, a supremum bound, and a positive waiting time;
they do not depend on the initial datum or final time horizon. No spatial
regularity of the solution is assumed in advance.

This proves the scalar-diffusion parabolic estimate used in Step 4. The
general matrix-diffusion equation still requires its eigenbasis version.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Planarwave

noncomputable section

universe u

section TimeChange

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict and reparametrize a regular BUC trajectory. -/
theorem BUCSpatialRegularOn.comp_time_on {s r : Set ℝ} {k : ℕ} {u : ℝ → BUC E F}
    (hu : BUCSpatialRegularOn s k u) {p : ℝ → ℝ} (hp : ContinuousOn p r)
    (hps : MapsTo p r s) : BUCSpatialRegularOn r k (fun t ↦ u (p t)) := by
  induction k generalizing F with
  | zero => exact hu.comp hp hps
  | succ k ih =>
    obtain ⟨hc, q, hq, hd⟩ := hu
    exact ⟨hc.comp hp hps, fun t ↦ q (p t), ih hq, fun t ht x ↦ hd _ (hps ht) x⟩

end TimeChange

variable {E V : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]

/-- The restarted mild equation on a finite horizon. It refers only to the
original solution and reaction, not to formal derivative equations. -/
def IsSemilinearHeatMildOn (a : ℝ) (f : V → V) (hf : Continuous f)
    (T : ℝ) (u : ℝ → BUC E V) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ T →
    u (s + t) = heatFlowBUC a t (u s) +
      heatDuhamel a (fun r ↦ BUC.postcompContinuous f hf (u (s + r))) t

omit [ProperSpace V] in
/-- Duhamel restarts with the translated source on the new time interval. -/
theorem heatDuhamel_restart_shift {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {g : ℝ → BUC E V} (hg : ContinuousOn g (Icc 0 (s + t))) :
    heatDuhamel a g (s + t) = heatFlowBUC a t (heatDuhamel a g s) +
      heatDuhamel a (fun r ↦ g (s + r)) t := by
  have hd := heatDuhamel_restart ha hs (show s ≤ s + t by linarith) g hg
  rw [add_sub_cancel_left] at hd
  rw [hd]
  congr 1
  unfold heatDuhamel
  have heq := intervalIntegral.integral_comp_add_left
    (fun r ↦ heatFlowBUC a (s + t - r) (g r)) s (a := 0) (b := t)
  simp only [add_zero] at heq
  simpa only [add_sub_add_left_eq_sub] using heq.symm

/-- The ordinary mild equation at time zero implies every restart formula;
the latter is not an independent hypothesis on a solution. -/
theorem isSemilinearHeatMildOn_of_mild {a T : ℝ} (ha : 0 ≤ a) (_hT : 0 ≤ T)
    (f : V → V) (hf : ContDiff ℝ ∞ f) {u : ℝ → BUC E V}
    (hu : ContinuousOn u (Icc 0 T))
    (hm : ∀ t ∈ Icc 0 T, u t = heatFlowBUC a t (u 0) +
      heatDuhamel a (fun r ↦ BUC.postcompContinuous f hf.continuous (u r)) t) :
    IsSemilinearHeatMildOn a f hf.continuous T u := by
  intro s t hs ht hst
  let g := fun r ↦ BUC.postcompContinuous f hf.continuous (u r)
  have hg : ContinuousOn g (Icc 0 T) :=
    (BUC.continuous_postcompContinuous f (hf.of_le (by simp))).comp_continuousOn hu
  have hsT : s ≤ T := by linarith
  rw [hm (s + t) ⟨add_nonneg hs ht, hst⟩, hm s ⟨hs, hsT⟩,
    heatFlowBUC_add, ← heatFlowBUC_add_apply ha ht hs]
  rw [heatDuhamel_restart_shift ha hs ht (hg.mono (Icc_subset_Icc le_rfl hst))]
  rw [add_comm t s, add_assoc]

/-- A bounded mild solution is spatially `C^k` after any positive waiting
time, with genuine BUC derivatives norm-continuous in time and a common
bound uniform over all horizons and bounded solution trajectories. -/
theorem exists_semilinearHeat_cn_bound (k : ℕ) {a δ B : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (_hB : 0 ≤ B) (f : V → V) (hf : ContDiff ℝ ∞ f) :
    ∃ C > 0, ∀ T : ℝ, 0 ≤ T → ∀ u : ℝ → BUC E V,
      ContinuousOn u (Icc 0 T) → (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      IsSemilinearHeatMildOn a f hf.continuous T u →
      BUCSpatialRegularOn (Icc δ T) k u ∧
        ∀ t ∈ Icc δ T, BUCSpatialBound k (u t) C := by
  induction k generalizing δ with
  | zero =>
    refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun T hT u hu hb hm ↦ ?_⟩
    exact ⟨hu.mono (Icc_subset_Icc hδ.le le_rfl),
      fun t ht ↦ (hb t ⟨hδ.le.trans ht.1, ht.2⟩).trans (le_max_left _ _)⟩
  | succ k ih =>
    have hhalf : 0 < δ / 2 := by positivity
    obtain ⟨A, hA, hAb⟩ := ih hhalf
    obtain ⟨R, hR, hRb⟩ := exists_bucSpatialBound_postcomp (E := E) k f hf A
    obtain ⟨H, hH, hHb⟩ := exists_bucSpatialBound_heatFlow (E := E) (F := V) (k + 1) ha hhalf
    let C := H * B + R * (δ / 2 + 2 * Real.sqrt (δ / 2) / Real.sqrt (2 * a))
    refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), fun T hT u hu hb hm ↦ ?_⟩
    obtain ⟨hreg, hbound⟩ := hAb T hT u hu hb hm
    have hsource {s L : ℝ} (hs : δ / 2 ≤ s) (hL : 0 ≤ L) (hsL : s + L ≤ T) :
        BUCSpatialRegularOn (Icc 0 L) k
          (fun r ↦ BUC.postcompContinuous f hf.continuous (u (s + r))) := by
      apply BUCSpatialRegularOn.postcomp_smooth _ f hf
      apply hreg.comp_time_on (continuous_const.add continuous_id).continuousOn
      intro r hr
      change s + r ∈ Icc (δ / 2) T
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hnew : BUCSpatialRegularOn (Icc δ T) (k + 1) u := by
      by_cases hδT : δ ≤ T
      · let s := δ / 2
        have hs : 0 ≤ s := hhalf.le
        have hL : 0 ≤ T - s := by dsimp only [s]; linarith
        have hsrc := hsource (s := s) (L := T - s) le_rfl hL (by ring_nf; exact le_rfl)
        have hduh := hsrc.heatDuhamel_gain ha hL
        have horbit := (bucSpatialRegularOn_heatFlow_of_age (k + 1) ha hhalf (u s)).mono
          (show Icc (δ / 2) (T - s) ⊆ Ici (δ / 2) from fun _ ht ↦ ht.1)
        have hsum := horbit.add (hduh.mono (Icc_subset_Icc hhalf.le le_rfl))
        have hshift := hsum.comp_time_on (r := Icc δ T)
          (p := fun t ↦ t - s) (continuous_id.sub continuous_const).continuousOn
          (by intro t ht; dsimp only [s]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        apply hshift.congr
        intro t ht
        have ht' : 0 ≤ t - s := by dsimp only [s]; linarith [ht.1]
        simpa only [add_sub_cancel] using (hm s (t - s) hs ht' (by linarith [ht.2])).symm
      · have hempty : Icc δ T = ∅ := Icc_eq_empty hδT
        rw [hempty]
        exact ((BUCSpatialRegularOn.zero (E := E) (F := V) univ (k + 1)).mono
          (empty_subset _)).congr (fun _ ht ↦ False.elim (notMem_empty _ ht))
    refine ⟨hnew, fun t ht ↦ ?_⟩
    let s := t - δ / 2
    have hs : δ / 2 ≤ s := by dsimp only [s]; linarith [ht.1]
    have hs0 : 0 ≤ s := hhalf.le.trans hs
    have hsT : s ≤ T := by dsimp only [s]; linarith [ht.2]
    have hst : s + δ / 2 = t := sub_add_cancel t (δ / 2)
    have hsrc := hsource hs hhalf.le (by rw [hst]; exact ht.2)
    have hsrcb : ∀ r ∈ Icc 0 (δ / 2),
        BUCSpatialBound k (BUC.postcompContinuous f hf.continuous (u (s + r))) R := by
      intro r hr
      exact hRb _ (hbound _ ⟨by linarith [hr.1], by linarith [hr.2, ht.2]⟩)
    have hd := hsrc.heatDuhamel_smoothing ha hsrcb
      (show δ / 2 ∈ Icc 0 (δ / 2) from ⟨hhalf.le, le_rfl⟩)
    have hh := (hHb (δ / 2) le_rfl (u s)).mono
      (mul_le_mul_of_nonneg_left (hb s ⟨hs0, hsT⟩) hH.le)
    have htotal := (hh.add hd).mono (le_max_left C 1)
    rw [← hm s (δ / 2) hs0 hhalf.le (by rw [hst]; exact ht.2), hst] at htotal
    exact htotal

/-- The uniform estimate for the usual, un-restarted mild equation. -/
theorem exists_semilinearHeat_cn_bound_of_mild (k : ℕ) {a δ B : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (hB : 0 ≤ B) (f : V → V) (hf : ContDiff ℝ ∞ f) :
    ∃ C > 0, ∀ T : ℝ, 0 ≤ T → ∀ u : ℝ → BUC E V,
      ContinuousOn u (Icc 0 T) → (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      (∀ t ∈ Icc 0 T, u t = heatFlowBUC a t (u 0) +
        heatDuhamel a (fun r ↦ BUC.postcompContinuous f hf.continuous (u r)) t) →
      BUCSpatialRegularOn (Icc δ T) k u ∧
        ∀ t ∈ Icc δ T, BUCSpatialBound k (u t) C := by
  obtain ⟨C, hC, hb⟩ := exists_semilinearHeat_cn_bound (E := E) k ha hδ hB f hf
  exact ⟨C, hC, fun T hT u hu hbound hm ↦
    hb T hT u hu hbound (isSemilinearHeatMildOn_of_mild ha.le hT f hf hu hm)⟩

/-- The cutoff version of the positive-time parabolic bound, including the
unsmoothed initial datum where the cutoff vanishes. Take `k = 9` in Step 4. -/
theorem exists_semilinearHeat_cutoff_cn_bound (k : ℕ) {a δ B : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (hB : 0 ≤ B) (f : V → V) (hf : ContDiff ℝ ∞ f) :
    ∃ C > 0, ∀ T : ℝ, 0 ≤ T → ∀ u : ℝ → BUC E V,
      ContinuousOn u (Icc 0 T) → (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      IsSemilinearHeatMildOn a f hf.continuous T u →
      ∀ χ : ℝ → ℝ, (∀ t < δ, χ t = 0) → (∀ t, |χ t| ≤ 1) →
      ∀ t ∈ Icc 0 T, BUCSpatialBound k (χ t • u t) C := by
  obtain ⟨C, hC, hb⟩ := exists_semilinearHeat_cn_bound (E := E) k ha hδ hB f hf
  refine ⟨C, hC, fun T hT u hu hbound hm χ hχ₀ hχ t ht ↦ ?_⟩
  by_cases hδt : δ ≤ t
  · exact (((hb T hT u hu hbound hm).2 t ⟨hδt, ht.2⟩).smul (χ t)).mono
      (by have := mul_le_mul_of_nonneg_right (hχ t) hC.le; simpa using this)
  · rw [hχ₀ t (lt_of_not_ge hδt), zero_smul]
    have hz : BUC.const E (0 : V) = (0 : BUC E V) := BUC.ext fun _ ↦ rfl
    simpa only [hz] using
      (BUCSpatialBound.const (E := E) k (0 : V)).mono (by simpa using hC.le)

end

end Planarwave
