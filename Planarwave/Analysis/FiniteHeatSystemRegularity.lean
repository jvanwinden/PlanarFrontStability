/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemilinearHeatRegularity

@[expose] public section

/-!
# Parabolic regularity for a finite coupled heat system

The linear diffusion is diagonal in fixed coordinates, but the reaction
may couple every component. Reconstruct the state by bounded linear maps
after scalar heat smoothing. Iteration on fixed-length backward intervals
gives all-order bounds independent of the final time horizon. This is the
eigenbasis form of the matrix parabolic estimate needed in Step 4.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

section Sum

universe u
variable {E : Type} {F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BUCSpatialBound.sum {ι : Type*} (I : Finset ι) {k : ℕ}
    {u : ι → BUC E F} {C : ι → ℝ} (hu : ∀ i ∈ I, BUCSpatialBound k (u i) (C i)) :
    BUCSpatialBound k (∑ i ∈ I, u i) (∑ i ∈ I, C i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have hz : BUC.const E (0 : F) = (0 : BUC E F) := BUC.ext fun _ ↦ rfl
    simpa only [Finset.sum_empty, hz, norm_zero] using BUCSpatialBound.const (E := E) k (0 : F)
  | @insert i I hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hu i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)))

end Sum

variable {E V ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]
  [Fintype ι]

/-- Scalar heat equations for fixed linear coordinates of a coupled vector
solution. The reaction is evaluated on the entire state. -/
def IsFiniteHeatSystemMildOn (a : ι → ℝ) (P : ι → V →L[ℝ] ℝ)
    (f : V → V) (hf : Continuous f) (T : ℝ) (u : ℝ → BUC E V) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ T → ∀ i,
    BUC.postcompCLM (P i) (u (s + t)) =
      heatFlowBUC (a i) t (BUC.postcompCLM (P i) (u s)) +
        heatDuhamel (a i) (fun r ↦
          BUC.postcompContinuous (fun v ↦ P i (f v)) ((P i).continuous.comp hf) (u (s + r))) t

/-- The coordinate equations at time zero imply all restart equations,
even though their nonlinear sources couple the components. -/
theorem isFiniteHeatSystemMildOn_of_mild (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → V →L[ℝ] ℝ) (f : V → V) (hf : ContDiff ℝ ∞ f)
    {T : ℝ} {u : ℝ → BUC E V} (hu : ContinuousOn u (Icc 0 T))
    (hm : ∀ t ∈ Icc 0 T, ∀ i,
      BUC.postcompCLM (P i) (u t) = heatFlowBUC (a i) t (BUC.postcompCLM (P i) (u 0)) +
        heatDuhamel (a i) (fun r ↦
          BUC.postcompContinuous (fun v ↦ P i (f v)) ((P i).continuous.comp hf.continuous) (u r)) t) :
    IsFiniteHeatSystemMildOn a P f hf.continuous T u := by
  intro s t hs ht hst i
  let g := fun r ↦ BUC.postcompContinuous (fun v ↦ P i (f v))
    ((P i).continuous.comp hf.continuous) (u r)
  have hg : ContinuousOn g (Icc 0 T) :=
    (BUC.continuous_postcompContinuous (fun v ↦ P i (f v))
      (((P i).contDiff.comp hf).of_le (by simp))).comp_continuousOn hu
  have hsT : s ≤ T := by linarith
  rw [hm (s + t) ⟨add_nonneg hs ht, hst⟩ i, hm s ⟨hs, hsT⟩ i,
    heatFlowBUC_add, ← heatFlowBUC_add_apply (ha i) ht hs]
  rw [heatDuhamel_restart_shift (ha i) hs ht (hg.mono (Icc_subset_Icc le_rfl hst))]
  rw [add_comm t s, add_assoc]

omit [CompleteSpace V] in
/-- Uniform higher regularity for coupled heat equations with distinct
positive diffusion rates. The reconstruction maps need not be isometries. -/
theorem exists_finiteHeatSystem_cn_bound (k : ℕ) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V)
    (hPQ : ∀ v : V, ∑ i, Q i (P i v) = v)
    {δ B : ℝ} (hδ : 0 < δ) (_hB : 0 ≤ B) (f : V → V) (hf : ContDiff ℝ ∞ f) :
    ∃ C > 0, ∀ T : ℝ, 0 ≤ T → ∀ u : ℝ → BUC E V,
      ContinuousOn u (Icc 0 T) → (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      IsFiniteHeatSystemMildOn a P f hf.continuous T u →
      BUCSpatialRegularOn (Icc δ T) k u ∧
        ∀ t ∈ Icc δ T, BUCSpatialBound k (u t) C := by
  classical
  induction k generalizing δ with
  | zero =>
    refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun T hT u hu hb hm ↦ ?_⟩
    exact ⟨hu.mono (Icc_subset_Icc hδ.le le_rfl),
      fun t ht ↦ (hb t ⟨hδ.le.trans ht.1, ht.2⟩).trans (le_max_left _ _)⟩
  | succ k ih =>
    have hhalf : 0 < δ / 2 := by positivity
    obtain ⟨A, hA, hAb⟩ := ih hhalf
    let fᵢ (i : ι) : V → ℝ := fun v ↦ P i (f v)
    have hfᵢ (i : ι) : ContDiff ℝ ∞ (fᵢ i) := (P i).contDiff.comp hf
    choose R hR hRb using fun i ↦ exists_bucSpatialBound_postcomp (E := E) k (fᵢ i) (hfᵢ i) A
    choose H hH hHb using fun i ↦
      exists_bucSpatialBound_heatFlow (E := E) (F := ℝ) (k + 1) (ha i) hhalf
    let Cᵢ (i : ι) := H i * (‖P i‖ * B) +
      R i * (δ / 2 + 2 * Real.sqrt (δ / 2) / Real.sqrt (2 * a i))
    let C := ∑ i, ‖Q i‖ * Cᵢ i
    refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), fun T hT u hu hb hm ↦ ?_⟩
    obtain ⟨hreg, hbound⟩ := hAb T hT u hu hb hm
    have hsource (i : ι) {s L : ℝ} (hs : δ / 2 ≤ s) (hsL : s + L ≤ T) :
        BUCSpatialRegularOn (Icc 0 L) k
          (fun r ↦ BUC.postcompContinuous (fᵢ i) (hfᵢ i).continuous (u (s + r))) := by
      apply BUCSpatialRegularOn.postcomp_smooth _ (fᵢ i) (hfᵢ i)
      apply hreg.comp_time_on (continuous_const.add continuous_id).continuousOn
      intro r hr
      change s + r ∈ Icc (δ / 2) T
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hreconstruct (t : ℝ) :
        (∑ i, BUC.postcompCLM (Q i) (BUC.postcompCLM (P i) (u t))) = u t := by
      apply BUC.ext
      intro x
      change (BUC.evalCLM (𝕜 := ℝ) x)
        (∑ i, BUC.postcompCLM (Q i) (BUC.postcompCLM (P i) (u t))) = u t x
      rw [map_sum]
      exact hPQ (u t x)
    have hcoord (i : ι) :
        BUCSpatialRegularOn (Icc δ T) (k + 1) (fun t ↦ BUC.postcompCLM (P i) (u t)) := by
      by_cases hδT : δ ≤ T
      · let s := δ / 2
        have hs : 0 ≤ s := hhalf.le
        have hL : 0 ≤ T - s := by dsimp only [s]; linarith
        have hsrc := hsource i (s := s) (L := T - s) le_rfl (by ring_nf; exact le_rfl)
        have hduh := hsrc.heatDuhamel_gain (ha i) hL
        have horbit := (bucSpatialRegularOn_heatFlow_of_age (k + 1) (ha i) hhalf
          (BUC.postcompCLM (P i) (u s))).mono
          (show Icc (δ / 2) (T - s) ⊆ Ici (δ / 2) from fun _ ht ↦ ht.1)
        have hsum := horbit.add (hduh.mono (Icc_subset_Icc hhalf.le le_rfl))
        have hshift := hsum.comp_time_on (r := Icc δ T)
          (p := fun t ↦ t - s) (continuous_id.sub continuous_const).continuousOn
          (by intro t ht; dsimp only [s]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        apply hshift.congr
        intro t ht
        have ht' : 0 ≤ t - s := by dsimp only [s]; linarith [ht.1]
        simpa only [add_sub_cancel] using (hm s (t - s) hs ht' (by linarith [ht.2]) i).symm
      · rw [Icc_eq_empty hδT]
        exact ((BUCSpatialRegularOn.zero (E := E) (F := ℝ) univ (k + 1)).mono
          (empty_subset _)).congr (fun _ ht ↦ False.elim (notMem_empty _ ht))
    have hnew : BUCSpatialRegularOn (Icc δ T) (k + 1) u := by
      have hi (i : ι) : BUCSpatialRegularOn (Icc δ T) (k + 1)
          (fun t ↦ BUC.postcompCLM (Q i) (BUC.postcompCLM (P i) (u t))) := by
        apply ((hcoord i).postcomp_smooth (Q i) (Q i).contDiff).congr
        intro t ht
        exact BUC.ext fun x ↦ rfl
      exact (BUCSpatialRegularOn.sum Finset.univ (fun i _ ↦ hi i)).congr
        (fun t _ ↦ hreconstruct t)
    refine ⟨hnew, fun t ht ↦ ?_⟩
    let s := t - δ / 2
    have hs : δ / 2 ≤ s := by dsimp only [s]; linarith [ht.1]
    have hs0 : 0 ≤ s := hhalf.le.trans hs
    have hsT : s ≤ T := by dsimp only [s]; linarith [ht.2]
    have hst : s + δ / 2 = t := sub_add_cancel t (δ / 2)
    have hcoordb (i : ι) : BUCSpatialBound (k + 1) (BUC.postcompCLM (P i) (u t)) (Cᵢ i) := by
      have hsrc := hsource i hs (L := δ / 2) (by rw [hst]; exact ht.2)
      have hsrcb : ∀ r ∈ Icc 0 (δ / 2),
          BUCSpatialBound k (BUC.postcompContinuous (fᵢ i) (hfᵢ i).continuous (u (s + r))) (R i) := by
        intro r hr
        exact hRb i _ (hbound _ ⟨by linarith [hr.1], by linarith [hr.2, ht.2]⟩)
      have hd := hsrc.heatDuhamel_smoothing (ha i) hsrcb
        (show δ / 2 ∈ Icc 0 (δ / 2) from ⟨hhalf.le, le_rfl⟩)
      have hh := (hHb i (δ / 2) le_rfl (BUC.postcompCLM (P i) (u s))).mono
        (mul_le_mul_of_nonneg_left
          ((BUC.norm_postcompCLM_apply_le (P i) (u s)).trans
            (mul_le_mul_of_nonneg_left (hb s ⟨hs0, hsT⟩) (norm_nonneg _))) (hH i).le)
      have htotal := hh.add hd
      rw [← hm s (δ / 2) hs0 hhalf.le (by rw [hst]; exact ht.2) i, hst] at htotal
      exact htotal
    have hsum := BUCSpatialBound.sum Finset.univ (fun i _ ↦ (hcoordb i).postcomp (Q i))
    rw [hreconstruct] at hsum
    exact hsum.mono (le_max_left C 1)

end

end Planarwave
