/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupLaplaceInversion

@[expose] public section

/-!
# From a sectorial spectral bound to semigroup growth

The spectral-to-growth theorem used in Lemmas 2.3--2.4 follows from differentiated
Laplace inversion and contour shifting. On positive times the shifted contour
bounds `t S(t)`; strong continuity supplies the bound on the initial time interval.
No decay assumption is imposed on the semigroup.
-/

open Filter MeasureTheory Set Topology

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

/-- A spectrum-free right half-plane and sectorial tail bounds imply a
semigroup growth bound at the boundary rate of that half-plane. -/
theorem exists_semigroup_bound_of_sectorial_resolvent (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {a C₀ Ω β : ℝ} (ha : 0 < a)
    (hsector : ∀ z : ℂ, Ω < z.re + a * |z.im| →
      ‖A.ambientResolvent z‖ ≤ C₀ / (z.re + a * |z.im| - Ω))
    (hres : ∀ z : ℂ, β ≤ z.re → A.IsInResolvent z) :
    ∃ M > 0, ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (β * t) := by
  obtain ⟨M₀, ω, _, _, hbound⟩ := S.exists_exponential_bound
  let γ := max ω β + 1
  have hωγ : ω < γ := by dsimp [γ]; linarith [le_max_left ω β]
  have hβγ : β ≤ γ := by dsimp [γ]; linarith [le_max_right ω β]
  have hstrip : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → A.IsInResolvent z := fun z hz _ ↦ hres z hz
  obtain ⟨C, _, hC⟩ := A.exists_ambientResolvent_vertical_bound ha hsector hstrip
  have hCγ (y : ℝ) : ‖A.ambientResolvent (γ + y * Complex.I)‖ ≤ C / (1 + |y|) := by
    simpa using hC (γ + y * Complex.I) (by simpa using hβγ) (by simp)
  obtain ⟨B, hB, hBbound⟩ := A.exists_integral_squaredResolventKernel_bound ha hsector
    (fun z hz ↦ hres z hz.ge)
  let B' := (2 * Real.pi)⁻¹ * B
  have hB' : 0 < B' := by dsimp [B']; positivity
  have hlarge (t : NNReal) (ht : 1 ≤ t) : ‖S t‖ ≤ B' * Real.exp (β * t) := by
    have htpos : 0 < (t : ℝ) := zero_lt_one.trans_le ht
    have hinv := A.time_smul_semigroup_eq_squaredResolvent_integral S hgen hbound hωγ hCγ htpos
    have hshift : (∫ y : ℝ, A.squaredResolventKernel (t : ℝ) (β + y * Complex.I)) =
        ∫ y : ℝ, A.squaredResolventKernel (t : ℝ) (γ + y * Complex.I) := by
      simpa using! A.integral_squaredResolventKernel_eq ha hβγ hsector hstrip t.2
    have hinv' : (t : ℝ) • S t = (2 * Real.pi)⁻¹ •
        ∫ y : ℝ, A.squaredResolventKernel (t : ℝ) (γ + y * Complex.I) := by
      simpa only [Real.toNNReal_coe] using! hinv
    rw [← hshift] at hinv'
    have hn := congrArg norm hinv'
    simp only [norm_smul, NNReal.norm_eq,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)] at hn
    have hh := mul_le_mul_of_nonneg_left (hBbound t t.2).2
      (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
    rw [← hn] at hh
    have hh' : (t : ℝ) * ‖S t‖ ≤ B' * Real.exp (β * t) := by
      simpa only [B', mul_assoc] using! hh
    exact (le_mul_of_one_le_left (norm_nonneg _) ht).trans hh'
  obtain ⟨L, hL, hlocal⟩ := S.exists_local_bound 1
  let M := max B' (L * Real.exp |β|)
  refine ⟨M, hB'.trans_le (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : 1 ≤ t
  · exact (hlarge t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have ht₁ : (t : ℝ) ≤ 1 := (le_of_not_ge ht)
    have hβt : -|β| ≤ β * (t : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right (neg_abs_le β) t.2
      have hh' : |β| * (t : ℝ) ≤ |β| := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left ht₁ (abs_nonneg β)
      exact (neg_le_neg hh').trans (by simpa only [neg_mul] using! hh)
    have hexp : 1 ≤ Real.exp |β| * Real.exp (β * t) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    calc
      ‖S t‖ ≤ L := hlocal t (le_of_not_ge ht)
      _ ≤ L * (Real.exp |β| * Real.exp (β * t)) :=
        le_mul_of_one_le_right (by linarith) hexp
      _ = (L * Real.exp |β|) * Real.exp (β * t) := (mul_assoc _ _ _).symm
      _ ≤ M * Real.exp (β * t) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Every rate strictly above a sectorial generator's spectral bound is a
valid semigroup growth rate. This is the direction required by the paper. -/
theorem exists_semigroup_bound_of_sectorial_spectrum (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {a C₀ Ω s β : ℝ} (ha : 0 < a)
    (hsector : ∀ z : ℂ, Ω < z.re + a * |z.im| →
      ‖A.ambientResolvent z‖ ≤ C₀ / (z.re + a * |z.im| - Ω))
    (hspec : ∀ z ∈ A.spectrum, z.re ≤ s) (hβ : s < β) :
    ∃ M > 0, ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (β * t) := by
  apply A.exists_semigroup_bound_of_sectorial_resolvent S hgen ha hsector
  intro z hz
  by_contra hnot
  have hs := hspec z hnot
  linarith

end

end Planarwave.ClosedOperator
