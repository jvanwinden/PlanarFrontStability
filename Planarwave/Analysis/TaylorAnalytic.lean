/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Taylor convergence from factorial derivative bounds

The real-time criterion for the analytic-semigroup argument requires an actual Taylor
identity, not just convergence of a formal series. We obtain it from the integral remainder,
for Banach-valued functions and increments of either sign.
-/

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A geometric bound on normalized derivatives bounds the Taylor remainder on a
real segment, in either direction from the expansion point. -/
theorem norm_taylor_remainder_le_of_factorial_bound {f : ℝ → F} {x h M K : ℝ}
    (_hM : 0 ≤ M) (_hK : 0 ≤ K) (n : ℕ)
    (hf : ∀ u ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + u * h))
    (hb : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖((n + 1).factorial : ℝ)⁻¹ • iteratedDeriv (n + 1) f (x + u * h)‖ ≤ M * K ^ (n + 1)) :
    ‖f (x + h) - ∑ k ∈ Finset.range (n + 1),
        h ^ k • ((k.factorial : ℝ)⁻¹ • iteratedDeriv k f x)‖ ≤
      M * (n + 1) * (K * ‖h‖) ^ (n + 1) := by
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv hf
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_fin, smul_eq_mul] at htaylor
  have hpoly : (∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℝ)⁻¹ • (h ^ k • iteratedDeriv k f x)) =
      ∑ k ∈ Finset.range (n + 1), h ^ k • ((k.factorial : ℝ)⁻¹ • iteratedDeriv k f x) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact smul_comm _ _ _
  rw [hpoly] at htaylor
  let R : ℝ → F := fun u ↦ ((n + 1 : ℝ) * (1 - u) ^ n * h ^ (n + 1)) •
    (((n + 1).factorial : ℝ)⁻¹ • iteratedDeriv (n + 1) f (x + u * h))
  have hrem : f (x + h) - ∑ k ∈ Finset.range (n + 1),
      h ^ k • ((k.factorial : ℝ)⁻¹ • iteratedDeriv k f x) = ∫ u in 0..1, R u := by
    rw [htaylor, add_sub_cancel_left, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only [R]
    simp only [smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [hrem]
  have hbound : ∀ u ∈ uIoc (0 : ℝ) 1, ‖R u‖ ≤ M * (n + 1) * (K * ‖h‖) ^ (n + 1) := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨(uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ hu).1.le,
      (uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ hu).2⟩
    have hpow : |1 - u| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) (by rw [abs_of_nonneg (by linarith [hu'.2])]; linarith [hu'.1])
    calc
      ‖R u‖ = ((n + 1) * |1 - u| ^ n * ‖h‖ ^ (n + 1)) *
          ‖((n + 1).factorial : ℝ)⁻¹ • iteratedDeriv (n + 1) f (x + u * h)‖ := by
        simp only [R, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_nonneg (show 0 ≤ (n + 1 : ℝ) by positivity)]
      _ ≤ ((n + 1) * 1 * ‖h‖ ^ (n + 1)) * (M * K ^ (n + 1)) := by
        apply mul_le_mul _ (hb u hu') (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Factorial derivative bounds ensure that the Taylor series sums to the function;
the conclusion includes negative increments, as required for a neighborhood expansion. -/
theorem hasSum_taylor_of_factorial_bound {f : ℝ → F} {x h M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hh : K * ‖h‖ < 1)
    (hf : ∀ n : ℕ, ∀ u ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ n f (x + u * h))
    (hb : ∀ n : ℕ, ∀ u ∈ Icc (0 : ℝ) 1,
      ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n f (x + u * h)‖ ≤ M * K ^ n) :
    HasSum (fun n ↦ h ^ n • ((n.factorial : ℝ)⁻¹ • iteratedDeriv n f x)) (f (x + h)) := by
  let b : ℕ → F := fun n ↦ h ^ n • ((n.factorial : ℝ)⁻¹ • iteratedDeriv n f x)
  have hsum : Summable (fun n ↦ ‖b n‖) := by
    apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) _
      ((summable_geometric_of_lt_one (by positivity) hh).mul_left M)
    intro n
    have hb₀ := hb n 0 (by simp)
    simp only [zero_mul, add_zero] at hb₀
    calc
      ‖b n‖ = ‖h‖ ^ n * ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n f x‖ := by
        simp only [b, norm_smul, norm_pow]
      _ ≤ ‖h‖ ^ n * (M * K ^ n) := mul_le_mul_of_nonneg_left hb₀ (by positivity)
      _ = M * (K * ‖h‖) ^ n := by rw [mul_pow]; ring
  apply (hasSum_iff_tendsto_nat_of_summable_norm hsum).mpr
  have hlim : Tendsto (fun n : ℕ ↦ M * (n + 1) * (K * ‖h‖) ^ (n + 1)) atTop (𝓝 0) := by
    have h := (tendsto_self_mul_const_pow_of_lt_one (by positivity : 0 ≤ K * ‖h‖) hh).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, mul_zero, mul_assoc] using h.const_mul M
  have hlim' : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), b k) atTop (𝓝 (f (x + h))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ norm_nonneg _) _ hlim
    intro n
    rw [norm_sub_rev]
    exact norm_taylor_remainder_le_of_factorial_bound hM hK n (hf (n + 1)) (hb (n + 1))
  exact (tendsto_add_atTop_iff_nat 1).mp hlim'

/-- Factorial bounds on a real neighborhood produce a holomorphic extension agreeing
with the original function there. This is the local analytic extension criterion used
for the longitudinal semigroup, with values in a complex Banach space. -/
theorem exists_bounded_analytic_extension_on_ball_of_factorial_bound
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {f : ℝ → F} {x δ M K : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (r : NNReal) (hr : 0 < r) (hrδ : (r : ℝ) ≤ δ) (hKr : K * r < 1)
    (hf : ∀ n : ℕ, ∀ y ∈ Metric.ball x δ, ContDiffAt ℝ n f y)
    (hb : ∀ n : ℕ, ∀ y ∈ Metric.ball x δ,
      ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n f y‖ ≤ M * K ^ n) :
    ∃ g : ℂ → F,
      AnalyticOnNhd ℂ g (Metric.ball (x : ℂ) r) ∧
      (∀ y : ℝ, |y - x| < r → g y = f y) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, ‖g z‖ ≤ M / (1 - K * r) := by
  let p : FormalMultilinearSeries ℂ ℂ F := fun n ↦
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
      ((n.factorial : ℝ)⁻¹ • iteratedDeriv n f x)
  have hrad : (r : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_bound M
    intro n
    have hb₀ := hb n x (Metric.mem_ball_self hδ)
    rw [show ‖p n‖ = ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n f x‖ from
      ContinuousMultilinearMap.norm_mkPiRing _]
    calc
      _ ≤ (M * K ^ n) * (r : ℝ) ^ n := mul_le_mul_of_nonneg_right hb₀ (by positivity)
      _ = M * (K * r) ^ n := by rw [mul_pow]; ring
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hKr.le) hM
      _ = M := mul_one _
  let g : ℂ → F := fun z ↦ p.sum (z - (x : ℂ))
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : z - (x : ℂ) ∈ Metric.eball (0 : ℂ) p.radius := by
      apply Metric.eball_subset_eball hrad
      simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using! hz
    have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w - (x : ℂ)) z := analyticAt_id.sub analyticAt_const
    exact (p.analyticOnNhd _ hz').comp (f := fun w : ℂ ↦ w - (x : ℂ)) hshift
  · intro y hy
    have hh : K * ‖y - x‖ < 1 := by
      rw [Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hy.le hK).trans_lt hKr
    have hseg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : x + u * (y - x) ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg hu.1]
      exact (mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _)).trans_lt
        (by simpa only [one_mul] using hy.trans_le hrδ)
    have hsum := hasSum_taylor_of_factorial_bound hM hK hh
      (fun n u hu ↦ hf n _ (hseg u hu)) (fun n u hu ↦ hb n _ (hseg u hu))
    have hcoe (a : ℝ) (v : F) : (a : ℂ) • v = a • v := by
      simpa only using! (RCLike.real_smul_eq_coe_smul (K := ℂ) a v).symm
    have hsum' : HasSum (fun n ↦ p n (fun _ ↦ (y : ℂ) - (x : ℂ))) (f y) := by
      simpa only [p, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
        Finset.card_fin, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
        hcoe, add_sub_cancel] using! hsum
    exact hsum'.tsum_eq
  · intro z hz
    have hz' : ‖z - (x : ℂ)‖ ≤ (r : ℝ) :=
      (show ‖z - (x : ℂ)‖ < r from by
        simpa only [Metric.mem_ball, dist_eq_norm] using hz).le
    have hgeom := (hasSum_geometric_of_lt_one (show 0 ≤ K * (r : ℝ) by positivity) hKr).mul_left M
    change ‖∑' n, p n (fun _ ↦ z - (x : ℂ))‖ ≤ _
    apply (tsum_of_norm_bounded hgeom ?_).trans_eq
      (show M * (1 - K * (r : ℝ))⁻¹ = M / (1 - K * r) by rw [div_eq_mul_inv])
    intro n
    calc
      ‖p n (fun _ ↦ z - (x : ℂ))‖ =
          ‖z - (x : ℂ)‖ ^ n * ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n f x‖ := by
        simp only [p, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
          Finset.card_fin, norm_smul, norm_pow]
      _ ≤ (r : ℝ) ^ n * (M * K ^ n) := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hz' n) (hb n x (Metric.mem_ball_self hδ))
        (norm_nonneg _) (by positivity)
      _ = M * (K * r) ^ n := by rw [mul_pow]; ring

/-- The qualitative form of the bounded Taylor extension criterion. -/
theorem exists_analytic_extension_on_ball_of_factorial_bound
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {f : ℝ → F} {x δ M K : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (r : NNReal) (hr : 0 < r) (hrδ : (r : ℝ) ≤ δ) (hKr : K * r < 1)
    (hf : ∀ n : ℕ, ∀ y ∈ Metric.ball x δ, ContDiffAt ℝ n f y)
    (hb : ∀ n : ℕ, ∀ y ∈ Metric.ball x δ,
      ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n f y‖ ≤ M * K ^ n) :
    ∃ g : ℂ → F,
      AnalyticOnNhd ℂ g (Metric.ball (x : ℂ) r) ∧
      ∀ y : ℝ, |y - x| < r → g y = f y := by
  obtain ⟨g, hg, heq, _⟩ := exists_bounded_analytic_extension_on_ball_of_factorial_bound
    hδ hM hK r hr hrδ hKr hf hb
  exact ⟨g, hg, heq⟩

/-- A convenient existential-radius form of the local holomorphic extension criterion. -/
theorem exists_analytic_extension_of_factorial_bound
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {f : ℝ → F} {x δ M K : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hf : ∀ n : ℕ, ∀ y ∈ Metric.ball x δ, ContDiffAt ℝ n f y)
    (hb : ∀ n : ℕ, ∀ y ∈ Metric.ball x δ,
      ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n f y‖ ≤ M * K ^ n) :
    ∃ r : NNReal, 0 < r ∧ (r : ℝ) ≤ δ ∧ ∃ g : ℂ → F,
      AnalyticOnNhd ℂ g (Metric.ball (x : ℂ) r) ∧
      ∀ y : ℝ, |y - x| < r → g y = f y := by
  let r : NNReal := ⟨min δ (1 / (K + 1)), by positivity⟩
  have hr : 0 < r := show 0 < min δ (1 / (K + 1)) from lt_min hδ (by positivity)
  have hrδ : (r : ℝ) ≤ δ := min_le_left _ _
  have hrK : (r : ℝ) ≤ 1 / (K + 1) := min_le_right _ _
  have hKr : K * r < 1 := by
    have h := (le_div_iff₀ (show 0 < K + 1 by positivity)).mp hrK
    have hr' : 0 < (r : ℝ) := hr
    nlinarith
  exact ⟨r, hr, hrδ, exists_analytic_extension_on_ball_of_factorial_bound hδ hM hK
    r hr hrδ hKr hf hb⟩

end

end Planarwave
