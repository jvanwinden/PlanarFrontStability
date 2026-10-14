/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Uniqueness for bounded pointwise BUC Volterra trajectories

The usual factorial iteration proves uniqueness even when the Volterra equation
has first been established after transverse evaluation. Local boundedness in
the BUC norm suffices. This avoids assuming full-norm time continuity before
identifying a Fourier formula with an independently constructed C₀ semigroup.
-/

open MeasureTheory Set Filter Topology

namespace Planarwave

noncomputable section

variable {V E : Type*} [UniformSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Repeated use of a homogeneous Volterra equation gains the factorial
denominator, with only a local supremum bound on the unknown trajectory. -/
theorem norm_bounded_pointwise_volterra_le (A : ℝ → BUC V E →L[ℂ] BUC V E)
    (w : ℝ → BUC V E) {L M T : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hA : ∀ s, 0 < s → ‖A s‖ ≤ L)
    (hw : ∀ t ∈ Ioc 0 T, ‖w t‖ ≤ M)
    (heq : ∀ t ∈ Ioc 0 T, ∀ z, w t z = ∫ r in 0..t, A (t-r) (w r) z)
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    ‖w t‖ ≤ (L ^ k / k.factorial) * M * t ^ k := by
  induction k generalizing t with
  | zero => simpa using hw t ht
  | succ k ih =>
    have ht0 : 0 ≤ t := ht.1.le
    apply (BUC.norm_le (by positivity)).mpr
    intro z
    rw [heq t ht z]
    have hint : IntervalIntegrable (fun r : ℝ ↦ ((L ^ (k+1) / k.factorial) * M) * r ^ k) volume 0 t :=
      (by fun_prop : Continuous (fun r : ℝ ↦ ((L ^ (k+1) / k.factorial) * M) * r ^ k)).intervalIntegrable 0 t
    have hb : ‖∫ r in 0..t, A (t-r) (w r) z‖ ≤
        ∫ r in 0..t, ((L ^ (k+1) / k.factorial) * M) * r ^ k := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.1.le _ hint
      filter_upwards [Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := t)] with r hr
      intro hrt
      have hro : r ∈ Ioo 0 t := hr.mpr hrt
      calc
        _ ≤ ‖A (t-r) (w r)‖ := BUC.norm_apply_le _ z
        _ ≤ ‖A (t-r)‖ * ‖w r‖ := (A (t-r)).le_opNorm _
        _ ≤ L * ((L ^ k / k.factorial) * M * r ^ k) :=
          mul_le_mul (hA _ (sub_pos.mpr hro.2)) (ih ⟨hro.1, hro.2.le.trans ht.2⟩)
            (norm_nonneg _) hL
        _ = _ := by rw [pow_succ]; ring
    apply hb.trans_eq
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp

/-- A locally bounded homogeneous pointwise Volterra trajectory vanishes.
No time continuity of the unknown BUC-valued path is presumed. -/
theorem bounded_pointwise_volterra_eq_zero (A : ℝ → BUC V E →L[ℂ] BUC V E)
    (w : ℝ → BUC V E) {L M T : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hA : ∀ s, 0 < s → ‖A s‖ ≤ L)
    (hw : ∀ t ∈ Ioc 0 T, ‖w t‖ ≤ M)
    (heq : ∀ t ∈ Ioc 0 T, ∀ z, w t z = ∫ r in 0..t, A (t-r) (w r) z)
    {t : ℝ} (ht : t ∈ Ioc 0 T) : w t = 0 := by
  have hb (k : ℕ) : ‖w t‖ ≤ ((L*t) ^ k / k.factorial) * M := by
    calc
      _ ≤ (L ^ k / k.factorial) * M * t ^ k :=
        norm_bounded_pointwise_volterra_le A w hL hM hA hw heq k ht
      _ = _ := by rw [mul_pow]; ring
  have hlim : Tendsto (fun k : ℕ ↦ ((L*t) ^ k / k.factorial) * M) atTop (𝓝 0) := by
    simpa using (Real.summable_pow_div_factorial (L*t)).tendsto_atTop_zero.mul_const M
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hb)) (norm_nonneg _))

/-- Two locally bounded trajectories with the same forcing term and integrable
pointwise Volterra terms coincide. -/
theorem bounded_pointwise_volterra_unique (A : ℝ → BUC V E →L[ℂ] BUC V E)
    (u v q : ℝ → BUC V E) {L M N T : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hA : ∀ s, 0 < s → ‖A s‖ ≤ L)
    (hu : ∀ t ∈ Ioc 0 T, ‖u t‖ ≤ M) (hv : ∀ t ∈ Ioc 0 T, ‖v t‖ ≤ N)
    (hiu : ∀ t ∈ Ioc 0 T, ∀ z, IntervalIntegrable (fun r ↦ A (t-r) (u r) z) volume 0 t)
    (hiv : ∀ t ∈ Ioc 0 T, ∀ z, IntervalIntegrable (fun r ↦ A (t-r) (v r) z) volume 0 t)
    (hequ : ∀ t ∈ Ioc 0 T, ∀ z, u t z = q t z + ∫ r in 0..t, A (t-r) (u r) z)
    (heqv : ∀ t ∈ Ioc 0 T, ∀ z, v t z = q t z + ∫ r in 0..t, A (t-r) (v r) z)
    {t : ℝ} (ht : t ∈ Ioc 0 T) : u t = v t := by
  apply sub_eq_zero.mp
  apply bounded_pointwise_volterra_eq_zero A (fun r ↦ u r - v r) hL (add_nonneg hM hN) hA
    (T := T) (M := M+N) (t := t) (ht := ht)
  · intro r hr
    exact (norm_sub_le _ _).trans (add_le_add (hu r hr) (hv r hr))
  · intro r hr z
    simp only [BUC.sub_apply, map_sub]
    rw [hequ r hr z, heqv r hr z, intervalIntegral.integral_sub (hiu r hr z) (hiv r hr z)]
    abel

end

end Planarwave
