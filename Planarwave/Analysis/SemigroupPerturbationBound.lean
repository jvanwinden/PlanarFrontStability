/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupPerturbation
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# Quantitative bounded-perturbation estimate

The Volterra series retains the original exponential weight at every iteration. Summing its
factorial majorant proves `‖T(t)‖ ≤ M exp ((ω + M ‖B‖) t)`, including negative `ω`. Keeping
the decay rate is essential for the frequency-uniform estimate in Lemma 2.2.
-/

open MeasureTheory Set

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Each Volterra iterate retains the free exponential weight and gains a factorial. -/
theorem norm_perturbationOperator_pow_freePath_le (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {M ω : ℝ} (hM : 0 ≤ M) (hbound : ∀ r : NNReal, ‖S r‖ ≤ M * Real.exp (ω * r))
    (T : NNReal) (x : E) (n : ℕ) (t : Icc (0 : ℝ) (T : ℝ)) :
    ‖((S.perturbationOperator B T) ^ n) (S.freePath T x) t‖ ≤
      M * Real.exp (ω * t) * ‖x‖ * ((M * ‖B‖) ^ n / n.factorial) * (t : ℝ) ^ n := by
  induction n generalizing t with
  | zero =>
    have h := ((S (t : ℝ).toNNReal).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg x))
    simpa [freePath, realOrbit, Real.coe_toNNReal _ t.2.1] using! h
  | succ n ih =>
    let v := ((S.perturbationOperator B T) ^ n) (S.freePath T x)
    let a := M * ‖B‖
    have hint : IntervalIntegrable
        (fun r : ℝ ↦ (M * Real.exp (ω * t) * ‖x‖ * (a ^ (n + 1) / n.factorial)) * r ^ n)
        volume 0 t := (by fun_prop : Continuous
          (fun r : ℝ ↦ (M * Real.exp (ω * t) * ‖x‖ * (a ^ (n + 1) / n.factorial)) * r ^ n)).intervalIntegrable 0 t
    have hnorm : ‖S.perturbationPath B T v t‖ ≤
        ∫ r in 0..(t : ℝ), (M * Real.exp (ω * t) * ‖x‖ *
          (a ^ (n + 1) / n.factorial)) * r ^ n := by
      change ‖∫ r in 0..(t : ℝ), S.realOrbit (B (extendTimePath v r)) ((t : ℝ) - r)‖ ≤ _
      apply intervalIntegral.norm_integral_le_of_norm_le t.2.1 _ hint
      apply Filter.Eventually.of_forall
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hr.1.le, hr.2.trans t.2.2⟩
      have hvr : ‖extendTimePath v r‖ ≤
          M * Real.exp (ω * r) * ‖x‖ * (a ^ n / n.factorial) * r ^ n := by
        rw [show extendTimePath v r = v ⟨r, hrT⟩ from extendTimePath_coe v ⟨r, hrT⟩]
        exact ih ⟨r, hrT⟩
      have hSr : ‖S ((t : ℝ) - r).toNNReal‖ ≤ M * Real.exp (ω * ((t : ℝ) - r)) := by
        simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr hr.2)] using hbound ((t : ℝ) - r).toNNReal
      have hexp : Real.exp (ω * ((t : ℝ) - r)) * Real.exp (ω * r) = Real.exp (ω * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        ‖S.realOrbit (B (extendTimePath v r)) ((t : ℝ) - r)‖ ≤
            ‖S ((t : ℝ) - r).toNNReal‖ * ‖B (extendTimePath v r)‖ :=
          (S ((t : ℝ) - r).toNNReal).le_opNorm _
        _ ≤ (M * Real.exp (ω * ((t : ℝ) - r))) * (‖B‖ * ‖extendTimePath v r‖) :=
          mul_le_mul hSr (B.le_opNorm _) (norm_nonneg _) (by positivity)
        _ ≤ (M * Real.exp (ω * ((t : ℝ) - r))) *
            (‖B‖ * (M * Real.exp (ω * r) * ‖x‖ * (a ^ n / n.factorial) * r ^ n)) := by
          gcongr
        _ = (Real.exp (ω * ((t : ℝ) - r)) * Real.exp (ω * r)) *
            (M * ‖x‖ * (a ^ (n + 1) / n.factorial) * r ^ n) := by dsimp [a]; rw [pow_succ]; ring
        _ = (M * Real.exp (ω * t) * ‖x‖ * (a ^ (n + 1) / n.factorial)) * r ^ n := by
          rw [hexp]; ring
    have heval : (∫ r in 0..(t : ℝ), (M * Real.exp (ω * t) * ‖x‖ *
          (a ^ (n + 1) / n.factorial)) * r ^ n) =
        M * Real.exp (ω * t) * ‖x‖ * (a ^ (n + 1) / (n + 1).factorial) *
          (t : ℝ) ^ (n + 1) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
    rw [heval] at hnorm
    simpa only [pow_succ', mul_apply_eq_comp, perturbationOperator_apply] using hnorm

/-- The perturbed trajectory is the pointwise sum of its Volterra iterates. -/
theorem perturbedOperator_eq_tsum (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (t : NNReal) (x : E) :
    S.perturbedOperator B t x =
      ∑' n : ℕ, ((S.perturbationOperator B t) ^ n) (S.freePath t x) ⟨t, t.2, le_rfl⟩ := by
  let L : (TimePath (E := E) t →L[ℂ] TimePath (E := E) t) →L[ℂ] E :=
    (ContinuousMap.evalCLM ℂ ⟨(t : ℝ), t.2, le_rfl⟩).comp
      (ContinuousLinearMap.apply ℂ (TimePath (E := E) t) (S.freePath t x))
  exact L.map_tsum (S.summable_perturbationOperator_pow B t)

/-- The bounded-perturbation growth estimate, with arbitrary real free growth rate. -/
theorem norm_boundedPerturbation_le (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {M ω : ℝ} (hM : 0 ≤ M) (hbound : ∀ r : NNReal, ‖S r‖ ≤ M * Real.exp (ω * r))
    (t : NNReal) :
    ‖S.boundedPerturbation B t‖ ≤ M * Real.exp ((ω + M * ‖B‖) * t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let a := M * ‖B‖ * (t : ℝ)
  let C := M * Real.exp (ω * t) * ‖x‖
  let v : ℕ → E := fun n ↦
    ((S.perturbationOperator B t) ^ n) (S.freePath t x) ⟨t, t.2, le_rfl⟩
  have hmajor : ∀ n, ‖v n‖ ≤ C * (a ^ n / n.factorial) := by
    intro n
    have h := S.norm_perturbationOperator_pow_freePath_le B hM hbound t x n ⟨t, t.2, le_rfl⟩
    convert h using 1
    dsimp [v, C, a]
    rw [mul_pow]
    ring
  have hs : Summable (fun n : ℕ ↦ C * (a ^ n / n.factorial)) :=
    (Real.summable_pow_div_factorial a).mul_left C
  have hsn : Summable (fun n ↦ ‖v n‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hmajor hs
  have hexp : (∑' n : ℕ, a ^ n / n.factorial) = Real.exp a := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  change ‖S.perturbedOperator B t x‖ ≤ _
  rw [S.perturbedOperator_eq_tsum]
  calc
    ‖∑' n : ℕ, v n‖ ≤ ∑' n : ℕ, ‖v n‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, C * (a ^ n / n.factorial) := hsn.tsum_le_tsum hmajor hs
    _ = C * Real.exp a := by rw [tsum_mul_left, hexp]
    _ = M * Real.exp ((ω + M * ‖B‖) * t) * ‖x‖ := by
      dsimp [C, a]
      rw [add_mul, Real.exp_add]
      ring

end

end C0Semigroup
