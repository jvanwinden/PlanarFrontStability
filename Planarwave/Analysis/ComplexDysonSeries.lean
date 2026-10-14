/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ComplexVolterra
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-! # Holomorphic Dyson--Volterra series for bounded perturbations -/

open Filter MeasureTheory Metric Set Topology

namespace Planarwave

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def complexDysonTerm (G : ℂ → (E →L[ℂ] E)) (B : E →L[ℂ] E) : ℕ → ℂ → (E →L[ℂ] E)
  | 0 => G
  | n + 1 => complexVolterra G B (complexDysonTerm G B n)

def complexDysonSum (G : ℂ → (E →L[ℂ] E)) (B : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  ∑' n : ℕ, complexDysonTerm G B n z

omit [CompleteSpace E] in
theorem norm_complexDysonTerm_le
    {η M ω : ℝ} (hM : 0 ≤ M) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖)) (n : ℕ)
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    ‖complexDysonTerm G B n z‖ ≤
      (M * (M * ‖B‖) ^ n / n.factorial) * Real.exp (ω * ‖z‖) * ‖z‖ ^ n := by
  induction n generalizing z with
  | zero => simpa only [complexDysonTerm, pow_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, div_one] using hG z hz
  | succ n ih =>
    have h := norm_complexVolterra_le hM (by positivity) B n hG (fun w hw ↦ ih hw) hz
    apply h.trans_eq
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ring

theorem analyticOnNhd_complexDysonTerm
    {η M ω : ℝ} (hM : 0 ≤ M) (hω : 0 ≤ ω) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hGa : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖)) (n : ℕ) :
    AnalyticOnNhd ℂ (complexDysonTerm G B n) (complexTimeSector η) := by
  induction n with
  | zero => exact hGa
  | succ n ih =>
    exact analyticOnNhd_complexVolterra hM (C := M * (M * ‖B‖) ^ n / n.factorial)
      (by positivity) hω B n hGa ih hG (fun _ hz ↦ norm_complexDysonTerm_le hM B hG n hz)

theorem summable_complexDysonTerm
    {η M ω : ℝ} (hM : 0 ≤ M) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    {z : ℂ} (hz : z ∈ complexTimeSector η) : Summable (fun n ↦ complexDysonTerm G B n z) := by
  apply Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (M * ‖B‖ * ‖z‖)).mul_left (M * Real.exp (ω * ‖z‖)))
  intro n
  convert norm_complexDysonTerm_le hM B hG n hz using 1
  rw [mul_pow]
  ring

omit [CompleteSpace E] in
/-- The series has the same perturbative exponential loss as the real-time
Volterra construction, now throughout the complex sector. -/
theorem norm_complexDysonSum_le
    {η M ω : ℝ} (hM : 0 ≤ M) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    ‖complexDysonSum G B z‖ ≤ M * Real.exp ((ω + M * ‖B‖) * ‖z‖) := by
  have hsum : HasSum (fun n : ℕ ↦ (M * Real.exp (ω * ‖z‖)) *
      ((M * ‖B‖ * ‖z‖) ^ n / n.factorial))
      ((M * Real.exp (ω * ‖z‖)) * Real.exp (M * ‖B‖ * ‖z‖)) := by
    have h := (Real.summable_pow_div_factorial (M * ‖B‖ * ‖z‖)).hasSum
    have hexp : (∑' n : ℕ, (M * ‖B‖ * ‖z‖) ^ n / n.factorial) =
        Real.exp (M * ‖B‖ * ‖z‖) := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hexp] at h
    exact h.mul_left _
  have hb : ‖complexDysonSum G B z‖ ≤
      (M * Real.exp (ω * ‖z‖)) * Real.exp (M * ‖B‖ * ‖z‖) := by
    apply tsum_of_norm_bounded hsum
    intro n
    convert norm_complexDysonTerm_le hM B hG n hz using 1
    rw [mul_pow]
    ring
  apply hb.trans_eq
  rw [add_mul, Real.exp_add]
  ring

/-- Local uniform convergence of the factorially bounded series preserves
holomorphy. There is no smallness condition on the bounded perturbation. -/
theorem analyticOnNhd_complexDysonSum
    {η M ω : ℝ} (hM : 0 ≤ M) (hω : 0 ≤ ω) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hGa : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖)) :
    AnalyticOnNhd ℂ (complexDysonSum G B) (complexTimeSector η) := by
  intro z hz
  let U := complexTimeSector η ∩ ball z 1
  let R := ‖z‖ + 1
  have hU : IsOpen U := (isOpen_complexTimeSector η).inter isOpen_ball
  have hzU : z ∈ U := ⟨hz, mem_ball_self zero_lt_one⟩
  have hmajor (n : ℕ) (w : ℂ) (hw : w ∈ U) :
      ‖complexDysonTerm G B n w‖ ≤ (M * Real.exp (ω * R)) * ((M * ‖B‖ * R) ^ n / n.factorial) := by
    have hnw : ‖w‖ ≤ R := by
      have h : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w - z) z
      have hd : ‖w - z‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw.2
      dsimp [R]
      linarith
    calc
      _ ≤ (M * (M * ‖B‖) ^ n / n.factorial) * Real.exp (ω * ‖w‖) * ‖w‖ ^ n :=
        norm_complexDysonTerm_le hM B hG n hw.1
      _ ≤ (M * (M * ‖B‖) ^ n / n.factorial) * Real.exp (ω * R) * R ^ n := by
        apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hnw n) (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnw hω)) (by positivity)
      _ = _ := by simp only [mul_pow]; ring
  exact (Complex.differentiableOn_tsum_of_summable_norm
    ((Real.summable_pow_div_factorial (M * ‖B‖ * R)).mul_left (M * Real.exp (ω * R)))
    (fun n ↦ (analyticOnNhd_complexDysonTerm hM hω B hGa hG n).differentiableOn.mono inter_subset_left)
    hU hmajor).analyticOnNhd hU z hzU

/-- The perturbation correction vanishes in operator norm at the time origin,
even though the free semigroup itself need not have an operator-norm limit there. -/
theorem norm_complexDysonSum_sub_le
    {η M ω : ℝ} (hM : 0 ≤ M) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    ‖complexDysonSum G B z - G z‖ ≤
      (M * Real.exp (ω * ‖z‖)) * (Real.exp (M * ‖B‖ * ‖z‖) - 1) := by
  let a := M * ‖B‖ * ‖z‖
  have hexp : HasSum (fun n : ℕ ↦ a ^ n / n.factorial) (Real.exp a) := by
    have h := (Real.summable_pow_div_factorial a).hasSum
    have heq : (∑' n : ℕ, a ^ n / n.factorial) = Real.exp a := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rwa [heq] at h
  have htail : HasSum (fun n : ℕ ↦ a ^ (n + 1) / (n + 1).factorial) (Real.exp a - 1) := by
    simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using
      (hasSum_nat_add_iff' 1).mpr hexp
  have hs := summable_complexDysonTerm hM B hG hz
  rw [complexDysonSum, hs.tsum_eq_zero_add]
  change ‖G z + (∑' n, complexDysonTerm G B (n + 1) z) - G z‖ ≤ _
  rw [add_sub_cancel_left]
  apply tsum_of_norm_bounded (htail.mul_left (M * Real.exp (ω * ‖z‖)))
  intro n
  convert norm_complexDysonTerm_le hM B hG (n + 1) hz using 1
  dsimp [a]
  rw [mul_pow]
  ring

theorem tendsto_complexDysonSum_sub_zero
    {η M ω : ℝ} (hM : 0 ≤ M) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖)) :
    Tendsto (fun z ↦ complexDysonSum G B z - G z) (𝓝[complexTimeSector η] 0) (𝓝 0) := by
  let b : ℂ → ℝ := fun z ↦ (M * Real.exp (ω * ‖z‖)) * (Real.exp (M * ‖B‖ * ‖z‖) - 1)
  have hb : Tendsto b (𝓝[complexTimeSector η] 0) (𝓝 0) := by
    have hc : Continuous b := by dsimp [b]; fun_prop
    simpa only [b, norm_zero, mul_zero, Real.exp_zero, sub_self] using
      (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := complexTimeSector η))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun z ↦ norm_nonneg _) _ hb
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact norm_complexDysonSum_sub_le hM B hG hz

theorem tendsto_complexDysonSum_zero
    {η M ω : ℝ} (hM : 0 ≤ M) {G : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x)) (x : E) :
    Tendsto (fun z ↦ complexDysonSum G B z x) (𝓝[complexTimeSector η] 0) (𝓝 x) := by
  have hd := ((ContinuousLinearMap.apply ℂ E x).continuous.continuousAt.tendsto).comp
    (tendsto_complexDysonSum_sub_zero hM B hG)
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    sub_apply, sub_add_cancel, zero_apply, zero_add] using! hd.add (hzero x)

end

end Planarwave
