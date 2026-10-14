/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupDuhamel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# Volterra series for a bounded semigroup perturbation

Iteration of the bounded-coefficient Duhamel operator gains `tⁿ / n!`. Consequently its
Neumann series converges on every finite time interval, not only on a small one. This yields
existence and uniqueness of continuous mild trajectories for the bounded perturbation invoked
in Lemma 2.2, without assuming continuity of the original semigroup in operator norm.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Repeated Volterra integration supplies the factorial denominator. -/
theorem norm_perturbationOperator_pow_apply_le (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (T : NNReal) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ r : NNReal, r ≤ T → ‖S r‖ ≤ M)
    (u : TimePath (E := E) T) (n : ℕ) (t : Icc (0 : ℝ) (T : ℝ)) :
    ‖((S.perturbationOperator B T) ^ n) u t‖ ≤
      ((M * ‖B‖) ^ n / n.factorial) * ‖u‖ * (t : ℝ) ^ n := by
  induction n generalizing t with
  | zero => simpa using u.norm_coe_le_norm t
  | succ n ih =>
    let v := ((S.perturbationOperator B T) ^ n) u
    let a := M * ‖B‖
    have ha : 0 ≤ a := by positivity
    have hint : IntervalIntegrable
        (fun r : ℝ ↦ ((a ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n) volume 0 t :=
      (by fun_prop : Continuous
        (fun r : ℝ ↦ ((a ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n)).intervalIntegrable 0 t
    have hnorm : ‖S.perturbationPath B T v t‖ ≤
        ∫ r in 0..(t : ℝ), ((a ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n := by
      change ‖∫ r in 0..(t : ℝ), S.realOrbit (B (extendTimePath v r)) ((t : ℝ) - r)‖ ≤ _
      apply intervalIntegral.norm_integral_le_of_norm_le t.2.1 _ hint
      apply Eventually.of_forall
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hr.1.le, hr.2.trans t.2.2⟩
      have htr : ((t : ℝ) - r).toNNReal ≤ T :=
        Real.toNNReal_le_iff_le_coe.mpr (by linarith [hr.1, t.2.2])
      have hvr : ‖extendTimePath v r‖ ≤ (a ^ n / n.factorial) * ‖u‖ * r ^ n := by
        rw [show extendTimePath v r = v ⟨r, hrT⟩ from extendTimePath_coe v ⟨r, hrT⟩]
        exact ih ⟨r, hrT⟩
      calc
        ‖S.realOrbit (B (extendTimePath v r)) ((t : ℝ) - r)‖ ≤
            ‖S ((t : ℝ) - r).toNNReal‖ * ‖B (extendTimePath v r)‖ :=
          (S ((t : ℝ) - r).toNNReal).le_opNorm _
        _ ≤ M * (‖B‖ * ‖extendTimePath v r‖) := by
          exact mul_le_mul (hbound _ htr) (B.le_opNorm _) (norm_nonneg _) hM
        _ = a * ‖extendTimePath v r‖ := by dsimp [a]; ring
        _ ≤ a * ((a ^ n / n.factorial) * ‖u‖ * r ^ n) := mul_le_mul_of_nonneg_left hvr ha
        _ = ((a ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n := by rw [pow_succ]; ring
    have heval : (∫ r in 0..(t : ℝ), ((a ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n) =
        (a ^ (n + 1) / (n + 1).factorial) * ‖u‖ * (t : ℝ) ^ (n + 1) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
    rw [heval] at hnorm
    simpa only [pow_succ', mul_apply_eq_comp, perturbationOperator_apply] using hnorm

/-- The Volterra powers have a summable operator-norm majorant on every finite interval. -/
theorem norm_perturbationOperator_pow_le (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (T : NNReal) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ r : NNReal, r ≤ T → ‖S r‖ ≤ M)
    (n : ℕ) : ‖(S.perturbationOperator B T) ^ n‖ ≤ (M * ‖B‖ * (T : ℝ)) ^ n / n.factorial := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    ‖((S.perturbationOperator B T) ^ n) u t‖ ≤
        ((M * ‖B‖) ^ n / n.factorial) * ‖u‖ * (t : ℝ) ^ n :=
      S.norm_perturbationOperator_pow_apply_le B T hM hbound u n t
    _ ≤ ((M * ‖B‖) ^ n / n.factorial) * ‖u‖ * (T : ℝ) ^ n := by
      gcongr
      · exact t.2.1
      · exact t.2.2
    _ = (M * ‖B‖ * (T : ℝ)) ^ n / n.factorial * ‖u‖ := by rw [mul_pow]; ring

/-- Convergence of the operator-valued Volterra series. -/
theorem summable_perturbationOperator_pow (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (T : NNReal) : Summable fun n : ℕ ↦ (S.perturbationOperator B T) ^ n := by
  obtain ⟨M, hM, hbound⟩ := S.exists_local_bound T
  apply Summable.of_norm_bounded
    (f := fun n : ℕ ↦ (S.perturbationOperator B T) ^ n)
    (Real.summable_pow_div_factorial (M * ‖B‖ * (T : ℝ)))
  intro n
  exact S.norm_perturbationOperator_pow_le B T (zero_le_one.trans hM) hbound n

/-- The Volterra equation is invertible without a smallness restriction on the time horizon. -/
theorem isUnit_one_sub_perturbationOperator (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (T : NNReal) : IsUnit (1 - S.perturbationOperator B T) := by
  let : IsTopologicalRing (TimePath (E := E) T →L[ℂ] TimePath (E := E) T) :=
    NonUnitalSeminormedRing.toIsTopologicalRing
      (α := TimePath (E := E) T →L[ℂ] TimePath (E := E) T)
  have hs := S.summable_perturbationOperator_pow B T
  exact ⟨⟨1 - S.perturbationOperator B T, ∑' n : ℕ, (S.perturbationOperator B T) ^ n,
    hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩, rfl⟩

/-- Every bounded perturbation has a unique continuous mild trajectory on any finite horizon. -/
theorem existsUnique_perturbedPath (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (T : NNReal) (x : E) :
    ∃! u : TimePath (E := E) T, ∀ t, u t = S.realOrbit x t + S.perturbationPath B T u t := by
  have hbij : Function.Bijective
      (1 - S.perturbationOperator B T : TimePath (E := E) T →L[ℂ] TimePath (E := E) T) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (S.isUnit_one_sub_perturbationOperator B T)
  obtain ⟨u, hu⟩ := hbij.surjective (S.freePath T x)
  refine ⟨u, ?_, ?_⟩
  · intro t
    have h := congrArg (fun v : TimePath (E := E) T ↦ v t) hu
    change u t - S.perturbationPath B T u t = S.realOrbit x t at h
    exact sub_eq_iff_eq_add.mp h
  · intro v hv
    apply hbij.injective
    rw [hu]
    ext t
    change v t - S.perturbationPath B T v t = S.realOrbit x t
    exact sub_eq_iff_eq_add.mpr (hv t)

/-- The free evolution as a bounded linear map from initial data into continuous paths. -/
def freePathOperator (S : C0Semigroup ℂ E) (T : NNReal) : E →L[ℂ] TimePath (E := E) T := by
  let M := (S.exists_local_bound T).choose
  have hM := (S.exists_local_bound T).choose_spec
  refine LinearMap.mkContinuous
    { toFun := S.freePath T
      map_add' := ?_
      map_smul' := ?_ } M ?_
  · intro x y
    ext t
    exact (S (t : ℝ).toNNReal).map_add x y
  · intro a x
    ext t
    exact (S (t : ℝ).toNNReal).map_smul a x
  · intro x
    apply (ContinuousMap.norm_le _ (mul_nonneg (zero_le_one.trans hM.1) (norm_nonneg x))).mpr
    intro t
    exact ((S (t : ℝ).toNNReal).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hM.2 _ (Real.toNNReal_le_iff_le_coe.mpr t.2.2)) (norm_nonneg x))

/-- The bounded inverse of `I - V` on a finite time interval. -/
def volterraInverse (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal) :
    TimePath (E := E) T →L[ℂ] TimePath (E := E) T :=
  ∑' n : ℕ, (S.perturbationOperator B T) ^ n

theorem volterraInverse_sub (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (v : TimePath (E := E) T) :
    S.volterraInverse B T v - S.perturbationOperator B T (S.volterraInverse B T v) = v := by
  let : IsTopologicalRing (TimePath (E := E) T →L[ℂ] TimePath (E := E) T) :=
    NonUnitalSeminormedRing.toIsTopologicalRing
      (α := TimePath (E := E) T →L[ℂ] TimePath (E := E) T)
  have h := (S.summable_perturbationOperator_pow B T).one_sub_mul_tsum_pow
  exact congrArg (fun L : TimePath (E := E) T →L[ℂ] TimePath (E := E) T ↦ L v) h

/-- The bounded linear solution map for the perturbed mild equation on a finite interval. -/
def perturbedPathOperator (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal) :
    E →L[ℂ] TimePath (E := E) T :=
  (S.volterraInverse B T).comp (S.freePathOperator T)

/-- The constructed solution map satisfies the full Duhamel equation. -/
theorem perturbedPathOperator_eq (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (x : E) (t : Icc (0 : ℝ) (T : ℝ)) :
    S.perturbedPathOperator B T x t = S.realOrbit x t +
      S.perturbationPath B T (S.perturbedPathOperator B T x) t := by
  have h := congrArg (fun u : TimePath (E := E) T ↦ u t)
    (S.volterraInverse_sub B T (S.freePathOperator T x))
  exact sub_eq_iff_eq_add.mp h

/-- In particular the mild trajectory has exactly the prescribed initial value. -/
@[simp]
theorem perturbedPathOperator_zero (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (x : E) : S.perturbedPathOperator B T x ⟨0, le_rfl, T.2⟩ = x := by
  rw [S.perturbedPathOperator_eq]
  simp [perturbationPath]

/-- Uniqueness identifies any other continuous mild trajectory with the constructed one. -/
theorem eq_perturbedPathOperator (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (x : E) (u : TimePath (E := E) T)
    (hu : ∀ t, u t = S.realOrbit x t + S.perturbationPath B T u t) :
    u = S.perturbedPathOperator B T x :=
  (S.existsUnique_perturbedPath B T x).unique hu (S.perturbedPathOperator_eq B T x)

end

end C0Semigroup
