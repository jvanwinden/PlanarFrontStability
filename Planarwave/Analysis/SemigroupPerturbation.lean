/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupVolterraSeries

@[expose] public section

/-!
# The semigroup of a bounded perturbation

The finite-horizon Volterra solutions agree on overlapping intervals. Uniqueness and the
time-splitting identity for the Duhamel integral then give a strongly continuous semigroup.
This is the bounded-perturbation construction used in the proof of Lemma 2.2 of the paper.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Restriction of a continuous trajectory to a smaller time interval. -/
def restrictTimePath {R T : NNReal} (hRT : R ≤ T) (u : TimePath (E := E) T) :
    TimePath (E := E) R :=
  ⟨fun t ↦ u ⟨t, t.2.1, t.2.2.trans (show (R : ℝ) ≤ T from hRT)⟩,
    u.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- Volterra integration only uses the trajectory before its evaluation time. -/
theorem perturbationPath_restrict (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {R T : NNReal} (hRT : R ≤ T) (u : TimePath (E := E) T)
    (t : Icc (0 : ℝ) (R : ℝ)) :
    S.perturbationPath B R (restrictTimePath hRT u) t =
      S.perturbationPath B T u ⟨t, t.2.1, t.2.2.trans (show (R : ℝ) ≤ T from hRT)⟩ := by
  apply intervalIntegral.integral_congr
  intro r hr
  have hrR : r ∈ Icc (0 : ℝ) (R : ℝ) :=
    ⟨(uIcc_of_le t.2.1 ▸ hr).1, (uIcc_of_le t.2.1 ▸ hr).2.trans t.2.2⟩
  have hrT : r ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hrR.1, hrR.2.trans hRT⟩
  change S.realOrbit (B (extendTimePath (restrictTimePath hRT u) r)) ((t : ℝ) - r) =
    S.realOrbit (B (extendTimePath u r)) ((t : ℝ) - r)
  rw [show extendTimePath (restrictTimePath hRT u) r = restrictTimePath hRT u ⟨r, hrR⟩
      from extendTimePath_coe _ ⟨r, hrR⟩,
    show extendTimePath u r = u ⟨r, hrT⟩ from extendTimePath_coe _ ⟨r, hrT⟩]
  rfl

/-- The mild solution is independent of the finite horizon on which it was constructed. -/
theorem perturbedPathOperator_restrict (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {R T : NNReal} (hRT : R ≤ T) (x : E) :
    restrictTimePath hRT (S.perturbedPathOperator B T x) = S.perturbedPathOperator B R x := by
  apply S.eq_perturbedPathOperator
  intro t
  rw [S.perturbationPath_restrict B hRT]
  exact S.perturbedPathOperator_eq B T x _

/-- Evaluation of the unique mild trajectory at the requested time. -/
def perturbedOperator (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (t : NNReal) : E →L[ℂ] E :=
  (ContinuousMap.evalCLM ℂ ⟨(t : ℝ), t.2, le_rfl⟩).comp (S.perturbedPathOperator B t)

/-- On any fixed finite interval the global family is the continuous Volterra solution. -/
theorem perturbedOperator_eq_path (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {t T : NNReal} (ht : t ≤ T) (x : E) :
    S.perturbedOperator B t x = S.perturbedPathOperator B T x ⟨t, t.2, ht⟩ := by
  exact (congrArg (fun u : TimePath (E := E) t ↦ u ⟨t, t.2, le_rfl⟩)
    (S.perturbedPathOperator_restrict B ht x)).symm

@[simp]
theorem perturbedOperator_zero (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (x : E) :
    S.perturbedOperator B 0 x = x :=
  S.perturbedPathOperator_zero B 0 x

/-- Strong continuity follows from the continuous solution on a fixed larger horizon. -/
theorem continuous_perturbedOperator (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (x : E) :
    Continuous (fun t : NNReal ↦ S.perturbedOperator B t x) := by
  rw [continuous_iff_continuousAt]
  intro t
  let T := t + 1
  have htT : t < T := by dsimp [T]; exact lt_add_one t
  have hcont : Continuous (fun r : NNReal ↦
      extendTimePath (S.perturbedPathOperator B T x) (r : ℝ)) :=
    (continuous_extendTimePath _).comp NNReal.continuous_coe
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds htT] with r hr
  rw [S.perturbedOperator_eq_path B hr.le]
  exact (extendTimePath_coe _ ⟨r, r.2, hr.le⟩).symm

/-- Splitting the forcing at time `s` transports its past and shifts its future. -/
theorem duhamel_time_add (S : C0Semigroup ℂ E) {f : ℝ → E} (hf : Continuous f)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.duhamel f (s + t) = S.realOrbit (S.duhamel f s) t +
      S.duhamel (fun r ↦ f (s + r)) t := by
  have hc (a : ℝ) : Continuous (fun r : ℝ ↦ S.realOrbit (f r) (a - r)) :=
    (S.continuous_duhamel_integrand hf).comp (continuous_const.prodMk continuous_id)
  unfold duhamel
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc (s + t)).intervalIntegrable 0 s) ((hc (s + t)).intervalIntegrable s (s + t))]
  congr 1
  · rw [realOrbit, ← (S t.toNNReal).intervalIntegral_comp_comm ((hc s).intervalIntegrable 0 s)]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) s := uIcc_of_le hs ▸ hr
    change S.realOrbit (f r) (s + t - r) = S t.toNNReal (S.realOrbit (f r) (s - r))
    rw [show s + t - r = t + (s - r) by ring,
      S.realOrbit_add (f r) ht (sub_nonneg.mpr hr'.2)]
  · calc
      (∫ r in s..s + t, S.realOrbit (f r) (s + t - r)) =
          ∫ r in 0..t, S.realOrbit (f (s + r)) (s + t - (s + r)) := by
        simpa only [add_zero] using
          (intervalIntegral.integral_comp_add_left
            (fun r ↦ S.realOrbit (f r) (s + t - r)) s (a := 0) (b := t)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r _
        dsimp only
        rw [show s + t - (s + r) = t - r by ring]

/-- The global mild trajectory, extended constantly to negative times. -/
def perturbedOrbit (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (x : E) (t : ℝ) : E :=
  S.perturbedOperator B t.toNNReal x

theorem continuous_perturbedOrbit (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (x : E) :
    Continuous (S.perturbedOrbit B x) :=
  (S.continuous_perturbedOperator B x).comp continuous_real_toNNReal

@[simp]
theorem perturbedOrbit_coe (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (x : E) (t : NNReal) :
    S.perturbedOrbit B x (t : ℝ) = S.perturbedOperator B t x := by
  simp [perturbedOrbit]

/-- The global trajectory satisfies Duhamel's formula at every nonnegative time. -/
theorem perturbedOrbit_eq (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (x : E)
    {t : ℝ} (ht : 0 ≤ t) :
    S.perturbedOrbit B x t = S.realOrbit x t +
      S.duhamel (fun r ↦ B (S.perturbedOrbit B x r)) t := by
  let T : NNReal := ⟨t, ht⟩
  have hp (r : ℝ) (hr : r ∈ Icc (0 : ℝ) t) :
      S.perturbedOrbit B x r = S.perturbedPathOperator B T x ⟨r, hr⟩ := by
    simpa only [perturbedOrbit, Real.coe_toNNReal _ hr.1] using
      S.perturbedOperator_eq_path B
        (t := r.toNNReal) (T := T) (Real.toNNReal_le_iff_le_coe.mpr hr.2) x
  rw [hp t ⟨ht, le_rfl⟩, S.perturbedPathOperator_eq]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) t := uIcc_of_le ht ▸ hr
  change S.realOrbit (B (extendTimePath (S.perturbedPathOperator B T x) r)) (t - r) =
    S.realOrbit (B (S.perturbedOrbit B x r)) (t - r)
  rw [hp r hr', show extendTimePath (S.perturbedPathOperator B T x) r =
    S.perturbedPathOperator B T x ⟨r, hr'⟩ from
      extendTimePath_coe (S.perturbedPathOperator B T x) ⟨r, hr'⟩]

/-- Continuous mild solutions on a finite interval agree with the global construction. -/
theorem eq_perturbedOperator_of_mild (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (T : NNReal) (x : E) {u : ℝ → E} (hu : Continuous u)
    (heq : ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      u t = S.realOrbit x t + S.duhamel (fun r ↦ B (u r)) t) :
    u T = S.perturbedOperator B T x := by
  let v : TimePath (E := E) T := ⟨fun t ↦ u t, hu.comp continuous_subtype_val⟩
  have hv : v = S.perturbedPathOperator B T x := by
    apply S.eq_perturbedPathOperator B T x
    intro t
    rw [show v t = u t from rfl, heq t t.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) (T : ℝ) :=
      ⟨(uIcc_of_le t.2.1 ▸ hr).1, (uIcc_of_le t.2.1 ▸ hr).2.trans t.2.2⟩
    change S.realOrbit (B (u r)) ((t : ℝ) - r) =
      S.realOrbit (B (extendTimePath v r)) ((t : ℝ) - r)
    rw [show extendTimePath v r = v ⟨r, hr'⟩ from extendTimePath_coe _ ⟨r, hr'⟩]
    rfl
  exact congrArg (fun w : TimePath (E := E) T ↦ w ⟨T, T.2, le_rfl⟩) hv

/-- Translating a mild trajectory starts the same equation at its current value. -/
theorem perturbedOrbit_time_add (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (x : E)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.perturbedOrbit B x (s + t) = S.realOrbit (S.perturbedOrbit B x s) t +
      S.duhamel (fun r ↦ B (S.perturbedOrbit B x (s + r))) t := by
  rw [S.perturbedOrbit_eq B x (add_nonneg hs ht),
    S.duhamel_time_add (f := fun r ↦ B (S.perturbedOrbit B x r))
      (B.continuous.comp (S.continuous_perturbedOrbit B x)) hs ht]
  rw [show S.realOrbit x (s + t) = S t.toNNReal (S.realOrbit x s) by
    rw [add_comm s t, S.realOrbit_add x ht hs]]
  rw [S.perturbedOrbit_eq B x hs]
  simp only [realOrbit, _root_.map_add, add_assoc]

/-- Uniqueness of the translated mild equation gives the semigroup law. -/
theorem perturbedOperator_add_apply (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (s t : NNReal) (x : E) :
    S.perturbedOperator B (s + t) x = S.perturbedOperator B t (S.perturbedOperator B s x) := by
  have hc : Continuous (fun r : ℝ ↦ S.perturbedOrbit B x ((s : ℝ) + r)) :=
    (S.continuous_perturbedOrbit B x).comp (continuous_const.add continuous_id)
  have h := S.eq_perturbedOperator_of_mild B t (S.perturbedOperator B s x) hc (by
    intro r hr
    change S.perturbedOrbit B x ((s : ℝ) + r) =
      S.realOrbit (S.perturbedOperator B s x) r +
        S.duhamel (fun a ↦ B (S.perturbedOrbit B x ((s : ℝ) + a))) r
    rw [← S.perturbedOrbit_coe B x s]
    exact S.perturbedOrbit_time_add B x s.2 hr.1)
  simpa only [← NNReal.coe_add, S.perturbedOrbit_coe] using h

/-- The strongly continuous semigroup obtained by bounded perturbation. -/
def boundedPerturbation (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) : C0Semigroup ℂ E where
  toFun := S.perturbedOperator B
  map_zero' := by ext x; exact S.perturbedOperator_zero B x
  map_add' := by
    intro s t
    ext x
    simpa only [add_comm t s, ContinuousLinearMap.comp_apply] using!
      S.perturbedOperator_add_apply B t s x
  strongContinuous' := S.continuous_perturbedOperator B

@[simp]
theorem boundedPerturbation_apply (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (t : NNReal) (x : E) :
    S.boundedPerturbation B t x = S.perturbedOperator B t x := rfl

@[simp]
theorem boundedPerturbation_realOrbit (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (x : E) (t : ℝ) :
    (S.boundedPerturbation B).realOrbit x t = S.perturbedOrbit B x t := rfl

end

end C0Semigroup
