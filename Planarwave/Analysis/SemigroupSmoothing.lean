/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Bounded generator smoothing and positive-time operator regularity

Quantitative heat smoothing gives bounded operators `A S(r)` for `r > 0`.
The results here convert that information into operator-norm time regularity,
without assuming uniform continuity of a C₀ semigroup at zero.
-/

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A bounded linear map whose range is in the generator domain and whose generator
values satisfy a uniform bound has a bounded generator composition. -/
theorem exists_generatorCompCLM (S : C0Semigroup ℂ E) (T : E →L[ℂ] E)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ∃ y, S.HasGeneratorAt (T x) y ∧ ‖y‖ ≤ C * ‖x‖) :
    ∃ B : E →L[ℂ] E, (∀ x, S.HasGeneratorAt (T x) (B x)) ∧ ‖B‖ ≤ C := by
  choose b hb hnorm using h
  let L : E →ₗ[ℂ] E :=
    { toFun := b
      map_add' := by
        intro x y
        apply (hb (x + y)).unique
        have h₁ : HasDerivWithinAt (S.realOrbit (T x)) (b x) (Ici 0) 0 := hb x
        have h₂ : HasDerivWithinAt (S.realOrbit (T y)) (b y) (Ici 0) 0 := hb y
        have heq : S.realOrbit (T (x + y)) = S.realOrbit (T x) + S.realOrbit (T y) := by
          funext t
          simp only [realOrbit, _root_.map_add, Pi.add_apply]
        change HasDerivWithinAt _ _ _ _
        rw [heq]
        exact h₁.add h₂
      map_smul' := by
        intro a x
        apply (hb (a • x)).unique
        have h₁ : HasDerivWithinAt (S.realOrbit (T x)) (b x) (Ici 0) 0 := hb x
        have heq : S.realOrbit (T (a • x)) = a • S.realOrbit (T x) := by
          funext t
          simp only [realOrbit, map_smul, Pi.smul_apply]
        change HasDerivWithinAt _ _ _ _
        rw [heq]
        exact h₁.const_smul a }
  let B := L.mkContinuous C hnorm
  exact ⟨B, hb, B.opNorm_le_bound hC hnorm⟩

/-- Smoothing at an earlier time gives a strong derivative for every subsequent orbit. -/
theorem hasDerivAt_realOrbit_of_generatorComp (S : C0Semigroup ℂ E)
    (r : NNReal) (B : E →L[ℂ] E)
    (hB : ∀ x, S.HasGeneratorAt (S r x) (B x)) {t : ℝ} (ht : (r : ℝ) < t) (x : E) :
    HasDerivAt (S.realOrbit x) (S.realOrbit (B x) (t - r)) t := by
  have hd := ((hB x).hasDerivAt (sub_pos.mpr ht)).scomp t
    ((hasDerivAt_id t).sub_const (r : ℝ))
  have hd' : HasDerivAt (fun s ↦ S.realOrbit (S r x) (s - r))
      (S.realOrbit (B x) (t - r)) t := by
    simpa only [Function.comp_def, id_eq, one_smul] using! hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  change S.realOrbit x s = S (s - r).toNNReal (S r x)
  simpa only [sub_add_cancel, realOrbit_coe] using!
    S.realOrbit_add x (s := s - (r : ℝ)) (t := (r : ℝ)) (sub_pos.mpr hs).le r.2

/-- A bound on `A S(r)` gives a Lipschitz estimate in operator norm on later bounded
time intervals. No operator-norm continuity at time zero is used. -/
theorem norm_operator_sub_le_of_generatorComp (S : C0Semigroup ℂ E)
    (r T : NNReal) (B : E →L[ℂ] E)
    (hB : ∀ x, S.HasGeneratorAt (S r x) (B x))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ s : NNReal, s ≤ T → ‖S s‖ ≤ M)
    {a b : ℝ} (ha : a ∈ Ioo (r : ℝ) ((r : ℝ) + T))
    (hb : b ∈ Ioo (r : ℝ) ((r : ℝ) + T)) :
    ‖S b.toNNReal - S a.toNNReal‖ ≤ M * ‖B‖ * ‖b - a‖ := by
  apply (S b.toNNReal - S a.toNNReal).opNorm_le_bound (by positivity)
  intro x
  have hderiv (s : ℝ) (hs : s ∈ Ioo (r : ℝ) ((r : ℝ) + T)) :
      HasDerivWithinAt (S.realOrbit x) (S.realOrbit (B x) (s - r))
        (Ioo (r : ℝ) ((r : ℝ) + T)) s :=
    (S.hasDerivAt_realOrbit_of_generatorComp r B hB hs.1 x).hasDerivWithinAt
  have hdBound (s : ℝ) (hs : s ∈ Ioo (r : ℝ) ((r : ℝ) + T)) :
      ‖S.realOrbit (B x) (s - r)‖ ≤ (M * ‖B‖) * ‖x‖ := by
    have hsT : (s - (r : ℝ)).toNNReal ≤ T :=
      Real.toNNReal_le_iff_le_coe.mpr (by linarith [hs.2])
    calc
      _ ≤ ‖S (s - r).toNNReal‖ * ‖B x‖ := (S _).le_opNorm _
      _ ≤ M * (‖B‖ * ‖x‖) :=
        mul_le_mul (hbound _ hsT) (B.le_opNorm x) (norm_nonneg _) hM
      _ = _ := by ring
  have h := (convex_Ioo (r : ℝ) ((r : ℝ) + T)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hdBound ha hb
  change ‖S.realOrbit x b - S.realOrbit x a‖ ≤ _
  exact h.trans_eq (by ring)

/-- Once `A S(r)` is bounded, the semigroup is operator-norm continuous at all times
strictly larger than `r`. -/
theorem continuousAt_operator_of_generatorComp (S : C0Semigroup ℂ E)
    (r : NNReal) (B : E →L[ℂ] E)
    (hB : ∀ x, S.HasGeneratorAt (S r x) (B x)) {t : ℝ} (ht : (r : ℝ) < t) :
    ContinuousAt (fun s : ℝ ↦ S s.toNNReal) t := by
  let T : NNReal := ⟨t + 1 - r, by linarith⟩
  obtain ⟨M, hM, hbound⟩ := S.exists_local_bound T
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have hLip : LipschitzOnWith ⟨M * ‖B‖, by positivity⟩ (fun s : ℝ ↦ S s.toNNReal)
      (Ioo (r : ℝ) ((r : ℝ) + T)) := by
    exact lipschitzOnWith_iff_norm_sub_le.mpr fun a ha b hb ↦
      S.norm_operator_sub_le_of_generatorComp r T B hB hM₀ hbound hb ha
  have hmem : t ∈ Ioo (r : ℝ) ((r : ℝ) + T) :=
    ⟨ht, by change t < (r : ℝ) + (t + 1 - r); linarith⟩
  exact (hLip.continuousOn t hmem).continuousAt (isOpen_Ioo.mem_nhds hmem)

/-- Two positive-time smoothing intervals upgrade the strong derivative to an
operator-norm derivative. The proof integrates the norm-continuous derivative and
checks the integral identity on each vector. -/
theorem hasDerivAt_operator_of_generatorComp (S : C0Semigroup ℂ E)
    (r : NNReal) (B : E →L[ℂ] E)
    (hB : ∀ x, S.HasGeneratorAt (S r x) (B x)) {t : ℝ} (ht : 2 * (r : ℝ) < t) :
    HasDerivAt (fun s : ℝ ↦ S s.toNNReal) ((S (t - r).toNNReal).comp B) t := by
  let a : ℝ := (t + 2 * r) / 2
  have hra : 2 * (r : ℝ) < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  let d : ℝ → (E →L[ℂ] E) := fun s ↦ (S (max s a - r).toNNReal).comp B
  have hd : Continuous d := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hrmax : (r : ℝ) < max s a - r := by linarith [le_max_right s a]
    have hp : ContinuousAt (fun u : ℝ ↦ max u a - (r : ℝ)) s := by fun_prop
    exact ((S.continuousAt_operator_of_generatorComp r B hB hrmax).comp
      (f := fun u : ℝ ↦ max u a - (r : ℝ)) hp).clm_comp continuousAt_const
  have hderiv (s : ℝ) (hs : a ≤ s) (x : E) :
      HasDerivAt (S.realOrbit x) (d s x) s := by
    have hrs : (r : ℝ) < s := by linarith [show 0 ≤ (r : ℝ) from r.2]
    simpa only [d, max_eq_left hs, ContinuousLinearMap.comp_apply, realOrbit] using!
      S.hasDerivAt_realOrbit_of_generatorComp r B hB hrs x
  have hintegral (s : ℝ) (hs : a ≤ s) :
      (∫ u in a..s, d u) = S s.toNNReal - S a.toNNReal := by
    ext x
    let ev : (E →L[ℂ] E) →L[ℝ] E := (ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ
    change ev (∫ u in a..s, d u) = S.realOrbit x s - S.realOrbit x a
    rw [← ev.intervalIntegral_comp_comm (hd.intervalIntegrable a s)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
      (S.continuous_realOrbit x).continuousOn (fun u hu ↦ hderiv u hu.1.le x)
      ((ev.continuous.comp hd).intervalIntegrable a s)
  have hdtime := (intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable a t)
    hd.aestronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt).add_const (S a.toNNReal)
  have hdval : d t = (S (t - r).toNNReal).comp B := by dsimp [d]; rw [max_eq_left hat.le]
  rw [hdval] at hdtime
  apply hdtime.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hat] with s hs
  rw [hintegral s hs.le, sub_add_cancel]

/-- Arbitrarily small positive smoothing times imply operator-norm differentiability
everywhere on the positive time axis. -/
theorem differentiableOn_operator_of_smoothing (S : C0Semigroup ℂ E)
    (hsmooth : ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : E →L[ℂ] E,
      ∀ x, S.HasGeneratorAt (S r x) (B x)) :
    DifferentiableOn ℝ (fun t : ℝ ↦ S t.toNNReal) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  let r : NNReal := ⟨min (t / 4) 1, by positivity⟩
  have hr : 0 < r := show 0 < min (t / 4) 1 from lt_min (by linarith [ht]) zero_lt_one
  have hr₁ : r ≤ 1 := show min (t / 4) 1 ≤ 1 from min_le_right _ _
  obtain ⟨B, hB⟩ := hsmooth r hr hr₁
  have hrt : 2 * (r : ℝ) < t := by
    change 2 * min (t / 4) 1 < t
    linarith [min_le_left (t / 4) 1, ht]
  exact (S.hasDerivAt_operator_of_generatorComp r B hB hrt).differentiableAt.differentiableWithinAt

/-- An operator-norm derivative is necessarily the generator applied after the semigroup. -/
theorem hasGeneratorAt_of_hasDerivAt_operator (S : C0Semigroup ℂ E)
    {t : ℝ} (ht : 0 ≤ t) {B : E →L[ℂ] E}
    (hd : HasDerivAt (fun s : ℝ ↦ S s.toNNReal) B t) (x : E) :
    S.HasGeneratorAt (S t.toNNReal x) (B x) := by
  have hx : HasDerivAt (S.realOrbit x) (B x) t :=
    ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have hshift := hx.scomp_of_eq 0 ((hasDerivAt_id 0).add_const t) (by simp)
  have hshift' : HasDerivWithinAt (fun u : ℝ ↦ S.realOrbit x (u + t)) (B x) (Ici 0) 0 := by
    simpa only [Function.comp_def, id_eq, one_smul] using! hshift.hasDerivWithinAt
  apply hshift'.congr
  · intro u hu
    exact (S.realOrbit_add x (s := u) (t := t) hu ht).symm
  · simp [realOrbit]

/-- Repeated positive-time splitting makes the operator-valued semigroup `C^k` for
every finite order. This is smoothness, not an assumption of analyticity. -/
theorem contDiffOn_nat_operator_of_smoothing (S : C0Semigroup ℂ E)
    (hsmooth : ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : E →L[ℂ] E,
      ∀ x, S.HasGeneratorAt (S r x) (B x)) (k : ℕ) :
    ContDiffOn ℝ k (fun t : ℝ ↦ S t.toNNReal) (Ioi 0) := by
  have hdiff := S.differentiableOn_operator_of_smoothing hsmooth
  induction k with
  | zero => exact contDiffOn_zero.mpr hdiff.continuousOn
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨hdiff, by simp, ?_⟩
    intro t ht
    change 0 < t at ht
    let r : NNReal := ⟨min (t / 4) 1, by positivity⟩
    have hr : 0 < r := show 0 < min (t / 4) 1 from lt_min (by positivity) zero_lt_one
    have hr₁ : r ≤ 1 := show min (t / 4) 1 ≤ 1 from min_le_right _ _
    obtain ⟨B, hB⟩ := hsmooth r hr hr₁
    have hrt : 2 * (r : ℝ) < t := by
      change 2 * min (t / 4) 1 < t
      linarith [min_le_left (t / 4) 1]
    have htr : 0 < t - (r : ℝ) := by linarith [show 0 ≤ (r : ℝ) from r.2]
    have hc : ContDiffAt ℝ k (fun s : ℝ ↦ (S (s - r).toNNReal).comp B) t := by
      have hshift : ContDiffAt ℝ k (fun s : ℝ ↦ s - (r : ℝ)) t := by fun_prop
      have hh : ContDiffAt ℝ k (fun s : ℝ ↦ S (s - r).toNNReal) t := by
        simpa only [Function.comp_def] using!
          (ih.contDiffAt (isOpen_Ioi.mem_nhds htr)).comp t hshift
      exact (((ContinuousLinearMap.compL ℂ E E E).flip B).restrictScalars ℝ).contDiff.contDiffAt.comp t hh
    apply (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [Ioi_mem_nhds hrt] with s hs
    exact (S.hasDerivAt_operator_of_generatorComp r B hB hs).deriv

/-- Positive-time operator-norm smoothness from bounded generator regularization. -/
theorem contDiffOn_infty_operator_of_smoothing (S : C0Semigroup ℂ E)
    (hsmooth : ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : E →L[ℂ] E,
      ∀ x, S.HasGeneratorAt (S r x) (B x)) :
    ContDiffOn ℝ ∞ (fun t : ℝ ↦ S t.toNNReal) (Ioi 0) :=
  contDiffOn_infty.mpr (S.contDiffOn_nat_operator_of_smoothing hsmooth)

end

end C0Semigroup
