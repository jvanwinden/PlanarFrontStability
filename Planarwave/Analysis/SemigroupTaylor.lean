/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupSmoothing
public import Planarwave.Analysis.TaylorAnalytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# Quantitative time derivatives of a smoothing semigroup

Splitting off equal positive time intervals expresses higher derivatives using powers
of the bounded operator `A S(r)`. The inverse-time smoothing bound then gives factorial
derivative estimates, the input for the analytic-semigroup step of Section 2.
-/

open Filter Set Topology
open scoped ContDiff

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Higher derivatives are obtained by splitting off one smoothing interval for each
generator factor. The leftover time is positive, so no norm derivative at zero is used. -/
theorem iteratedDeriv_operator_eq_of_generatorComp (S : C0Semigroup ℂ E)
    (r : NNReal) (B : E →L[ℂ] E)
    (hB : ∀ x, S.HasGeneratorAt (S r x) (B x)) (k : ℕ) {t : ℝ}
    (ht : (k + 1 : ℝ) * r < t) :
    iteratedDeriv k (fun s : ℝ ↦ S s.toNNReal) t =
      (S (t - k * r).toNNReal).comp (B ^ k) := by
  induction k generalizing t with
  | zero => simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, sub_zero, pow_zero]; rfl
  | succ k ih =>
    have hr₀ : 0 ≤ (r : ℝ) := r.2
    have hkt : (k + 1 : ℝ) * r < t := by push_cast at ht; nlinarith
    have hd := (S.hasDerivAt_operator_of_generatorComp r B hB
      (t := t - k * r) (by push_cast at ht; linarith)).scomp t
      ((hasDerivAt_id t).sub_const ((k : ℝ) * r))
    have hd' : HasDerivAt (fun s : ℝ ↦ S (s - k * r).toNNReal)
        ((S (t - k * r - r).toNNReal).comp B) t := by
      simpa only [Function.comp_def, id_eq, one_smul] using! hd
    let L : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) :=
      ((ContinuousLinearMap.compL ℂ E E E).flip (B ^ k)).restrictScalars ℝ
    have hprod := L.hasFDerivAt.comp_hasDerivAt t hd'
    have heq : iteratedDeriv k (fun s : ℝ ↦ S s.toNNReal) =ᶠ[𝓝 t]
        (fun s : ℝ ↦ (S (s - k * r).toNNReal).comp (B ^ k)) := by
      filter_upwards [Ioi_mem_nhds hkt] with s hs
      exact ih hs
    rw [iteratedDeriv_succ]
    rw [heq.deriv_eq]
    have hval : L ((S (t - k * r - r).toNNReal).comp B) =
        (S (t - (k + 1 : ℕ) * r).toNNReal).comp (B ^ (k + 1)) := by
      have htval : t - k * (r : ℝ) - r = t - (k + 1 : ℕ) * r := by push_cast; ring
      change ((S _).comp B).comp (B ^ k) = _
      rw [htval, ContinuousLinearMap.comp_assoc, pow_succ']
      rfl
    simpa only [L, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.coe_restrictScalars] using! hprod.deriv.trans hval

/-- A uniform `C/r` smoothing bound gives quantitative bounds on every derivative
on a bounded time interval separated from zero. -/
theorem norm_iteratedDeriv_operator_le (S : C0Semigroup ℂ E)
    {T : NNReal} {M C a t : ℝ} (hM : 0 ≤ M) (_hC : 0 ≤ C) (ha : 0 < a)
    (ha₁ : a ≤ 1) (hat : a ≤ t) (htT : t ≤ T)
    (hbound : ∀ s : NNReal, s ≤ T → ‖S s‖ ≤ M)
    (hsmooth : ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : E →L[ℂ] E,
      (∀ x, S.HasGeneratorAt (S r x) (B x)) ∧ ‖B‖ ≤ C / (r : ℝ)) (k : ℕ) :
    ‖iteratedDeriv k (fun s : ℝ ↦ S s.toNNReal) t‖ ≤
      M * (2 * C * (k + 1) / a) ^ k := by
  have hk : 0 < (k + 1 : ℝ) := by positivity
  let r : NNReal := ⟨a / (2 * (k + 1)), by positivity⟩
  have hr : 0 < r := show 0 < a / (2 * (k + 1)) from div_pos ha (by positivity)
  have hra : (r : ℝ) ≤ a := by
    change a / (2 * (k + 1)) ≤ a
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [show 0 ≤ (k : ℝ) by positivity]
  have hr₁ : r ≤ 1 := show (r : ℝ) ≤ 1 from hra.trans ha₁
  have htime : (k + 1 : ℝ) * r < t := by
    have heq : (k + 1 : ℝ) * r = a / 2 := by
      change (k + 1 : ℝ) * (a / (2 * (k + 1))) = a / 2
      field_simp
    rw [heq]
    linarith
  obtain ⟨B, hB, hnorm⟩ := hsmooth r hr hr₁
  rw [S.iteratedDeriv_operator_eq_of_generatorComp r B hB k htime]
  have hrem : (t - k * (r : ℝ)).toNNReal ≤ T := by
    apply Real.toNNReal_le_iff_le_coe.mpr
    have hkr : 0 ≤ (k : ℝ) * r := mul_nonneg (by positivity) r.2
    linarith
  have hpow : ‖B ^ k‖ ≤ ‖B‖ ^ k := by
    rcases k.eq_zero_or_pos with rfl | hkpos
    · apply (B ^ 0).opNorm_le_bound (by simp)
      intro x
      simp
    · exact norm_pow_le' B hkpos
  calc
    _ ≤ ‖S (t - k * r).toNNReal‖ * ‖B ^ k‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * (C / (r : ℝ)) ^ k := mul_le_mul (hbound _ hrem)
      (hpow.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm k))
      (norm_nonneg _) hM
    _ = _ := by
      congr 2
      change C / (a / (2 * (k + 1))) = 2 * C * (k + 1) / a
      field_simp

/-- Normalizing by `k!` leaves a geometric bound. This is stronger than mere smoothness
and supplies a positive radius for the time Taylor series. -/
theorem norm_factorial_inv_smul_iteratedDeriv_operator_le (S : C0Semigroup ℂ E)
    {T : NNReal} {M C a t : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (ha : 0 < a)
    (ha₁ : a ≤ 1) (hat : a ≤ t) (htT : t ≤ T)
    (hbound : ∀ s : NNReal, s ≤ T → ‖S s‖ ≤ M)
    (hsmooth : ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : E →L[ℂ] E,
      (∀ x, S.HasGeneratorAt (S r x) (B x)) ∧ ‖B‖ ≤ C / (r : ℝ)) (k : ℕ) :
    ‖(k.factorial : ℝ)⁻¹ • iteratedDeriv k (fun s : ℝ ↦ S s.toNNReal) t‖ ≤
      (M * Real.exp 1) * (2 * Real.exp 1 * C / a) ^ k := by
  have hb := S.norm_iteratedDeriv_operator_le hM hC ha ha₁ hat htT hbound hsmooth k
  have hf : 0 < (k.factorial : ℝ) := by positivity
  have hexp : (k + 1 : ℝ) ^ k / k.factorial ≤ Real.exp 1 * (Real.exp 1) ^ k := by
    have h := Real.pow_div_factorial_le_exp (k + 1 : ℝ) (show 0 ≤ (k + 1 : ℝ) by positivity) k
    rw [Real.exp_add, show Real.exp (k : ℝ) = Real.exp 1 ^ k by
      simpa only [mul_one] using Real.exp_nat_mul 1 k] at h
    simpa only [mul_comm] using h
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hf)]
  calc
    _ ≤ (k.factorial : ℝ)⁻¹ * (M * (2 * C * (k + 1) / a) ^ k) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (M * (2 * C / a) ^ k) * ((k + 1 : ℝ) ^ k / k.factorial) := by
      rw [show 2 * C * (k + 1) / a = (2 * C / a) * (k + 1) by ring, mul_pow]
      ring
    _ ≤ (M * (2 * C / a) ^ k) * (Real.exp 1 * (Real.exp 1) ^ k) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by rw [show 2 * Real.exp 1 * C / a = (2 * C / a) * Real.exp 1 by ring, mul_pow]; ring

/-- A common inverse-time smoothing constant supplies holomorphic time extensions
on neighborhoods chosen uniformly over the semigroup family. Each extension agrees
with the actual semigroup on the real diameter, not just at its center. -/
theorem exists_uniform_bounded_analytic_extension_of_smoothing {ι : Type*}
    (S : ι → C0Semigroup ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (hsmooth : ∀ i, ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : E →L[ℂ] E,
      (∀ x, (S i).HasGeneratorAt (S i r x) (B x)) ∧ ‖B‖ ≤ C / (r : ℝ)) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ L > 0, ∀ t : ℝ, 0 < t → ∀ i,
      ∀ M : ℝ, 0 ≤ M →
      (∀ s : NNReal, (s : ℝ) ≤ 2 * t → ‖S i s‖ ≤ M) →
      ∃ g : ℂ → (E →L[ℂ] E),
      AnalyticOnNhd ℂ g (Metric.ball (t : ℂ) (η * min t 1)) ∧
      (∀ s : ℝ, |s - t| < η * min t 1 → g s = S i s.toNNReal) ∧
      ∀ z ∈ Metric.ball (t : ℂ) (η * min t 1), ‖g z‖ ≤ L * M := by
  let η : ℝ := 1 / (4 * (Real.exp 1 * C + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη₁ : η ≤ 1 / 2 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (Real.exp_pos 1).le hC]
  have hηC : 4 * Real.exp 1 * C * η < 1 := by
    dsimp [η]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    linarith
  let L : ℝ := Real.exp 1 / (1 - 4 * Real.exp 1 * C * η)
  have hL : 0 < L := div_pos (Real.exp_pos 1) (sub_pos.mpr hηC)
  refine ⟨η, hη, hη₁, L, hL, fun t ht i M hM₀ hbound ↦ ?_⟩
  let a : ℝ := min (t / 2) 1
  have ha : 0 < a := lt_min (by positivity) zero_lt_one
  have ha₁ : a ≤ 1 := min_le_right _ _
  let K : ℝ := 2 * Real.exp 1 * C / a
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let r : NNReal := ⟨η * min t 1, by positivity⟩
  have hr : 0 < r := show 0 < η * min t 1 from mul_pos hη (lt_min ht zero_lt_one)
  have hrt : (r : ℝ) ≤ t / 2 := by
    change η * min t 1 ≤ t / 2
    calc
      _ ≤ (1 / 2) * t := mul_le_mul hη₁ (min_le_left _ _) (le_of_lt (lt_min ht zero_lt_one)) (by positivity)
      _ = _ := by ring
  have hmina : min t 1 ≤ 2 * a := by
    dsimp [a]
    rcases le_total (t / 2) 1 with h | h
    · rw [min_eq_left h]
      linarith [min_le_left t 1]
    · rw [min_eq_right h]
      linarith [min_le_right t 1]
  have hKr_le : K * r ≤ 4 * Real.exp 1 * C * η := by
    calc
      K * r ≤ K * (η * (2 * a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmina hη.le) hK
      _ = 4 * Real.exp 1 * C * η := by dsimp [K]; field_simp; ring
  have hKr : K * r < 1 := hKr_le.trans_lt hηC
  let T : NNReal := ⟨2 * t, by positivity⟩
  have hs : ∀ u : NNReal, 0 < u → u ≤ 1 → ∃ B : E →L[ℂ] E,
      ∀ x, (S i).HasGeneratorAt (S i u x) (B x) := by
    intro u hu hu₁
    obtain ⟨B, hB, _⟩ := hsmooth i u hu hu₁
    exact ⟨B, hB⟩
  have hmem {s : ℝ} (hs : s ∈ Metric.ball t (t / 2)) : a ≤ s ∧ s ≤ T ∧ 0 < s := by
    have habs : |s - t| < t / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
    have hlo := (abs_lt.mp habs).1
    have hhi := (abs_lt.mp habs).2
    have ha₂ : a ≤ t / 2 := min_le_left _ _
    change a ≤ s ∧ s ≤ 2 * t ∧ 0 < s
    constructor
    · linarith
    · constructor <;> linarith
  have hf : ∀ n : ℕ, ∀ s ∈ Metric.ball t (t / 2),
      ContDiffAt ℝ n (fun s : ℝ ↦ S i s.toNNReal) s := by
    intro n s hst
    exact ((S i).contDiffOn_nat_operator_of_smoothing hs n).contDiffAt
      (isOpen_Ioi.mem_nhds (hmem hst).2.2)
  have hb : ∀ n : ℕ, ∀ s ∈ Metric.ball t (t / 2),
      ‖(n.factorial : ℝ)⁻¹ • iteratedDeriv n (fun s : ℝ ↦ S i s.toNNReal) s‖ ≤
        (M * Real.exp 1) * K ^ n := by
    intro n s hst
    exact (S i).norm_factorial_inv_smul_iteratedDeriv_operator_le hM₀ hC ha ha₁
      (hmem hst).1 (hmem hst).2.1 (fun s hs ↦ hbound s hs) (hsmooth i) n
  obtain ⟨g, hg, heq, hnorm⟩ := Planarwave.exists_bounded_analytic_extension_on_ball_of_factorial_bound
    (f := fun s : ℝ ↦ S i s.toNNReal) (M := M * Real.exp 1) (K := K)
    (show 0 < t / 2 by positivity) (by positivity) hK r hr hrt hKr hf hb
  refine ⟨g, hg, heq, fun z hz ↦ (hnorm z hz).trans ?_⟩
  calc
    (M * Real.exp 1) / (1 - K * r) ≤
        (M * Real.exp 1) / (1 - 4 * Real.exp 1 * C * η) :=
      div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hηC) (by linarith)
    _ = L * M := by dsimp [L]; ring

/-- The qualitative local extension needs only local boundedness, which follows
from strong continuity of each member of the semigroup family. -/
theorem exists_uniform_analytic_extension_of_smoothing {ι : Type*}
    (S : ι → C0Semigroup ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (hsmooth : ∀ i, ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : E →L[ℂ] E,
      (∀ x, (S i).HasGeneratorAt (S i r x) (B x)) ∧ ‖B‖ ≤ C / (r : ℝ)) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → ∀ i, ∃ g : ℂ → (E →L[ℂ] E),
      AnalyticOnNhd ℂ g (Metric.ball (t : ℂ) (η * min t 1)) ∧
      ∀ s : ℝ, |s - t| < η * min t 1 → g s = S i s.toNNReal := by
  obtain ⟨η, hη, hη₁, L, hL, hext⟩ :=
    exists_uniform_bounded_analytic_extension_of_smoothing S hC hsmooth
  refine ⟨η, hη, hη₁, fun t ht i ↦ ?_⟩
  obtain ⟨M, hM, hb⟩ := (S i).exists_local_bound ⟨2 * t, by positivity⟩
  obtain ⟨g, hg, heq, _⟩ := hext t ht i M (zero_le_one.trans hM) (fun s hs ↦ hb s hs)
  exact ⟨g, hg, heq⟩

end

end C0Semigroup
