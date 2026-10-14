/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSectorialResolvent
import all Planarwave.Analysis.FrontHighFrequencySemigroup
import Planarwave.Analysis.SemigroupSpectralGrowth

/-!
# Mid- and high-frequency semigroup bounds

Complete Lemma 2.4 in the paper's order: obtain individual decay from the
transverse spectral gap, uniformize on the compact intermediate-frequency
annulus, combine with the high-frequency estimate, and use the bounded
imaginary-frequency perturbation. Finally include the scalar heat multiplier.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- The actual longitudinal pencil inherits every growth rate strictly above
its spectral bound. Sectoriality has already been proved from the front data. -/
theorem exists_frontPencil_bound_of_spectrum (q : ℂ) {s β : ℝ}
    (hspec : ∀ z ∈ (frontPencilClosedOperator f D c φ h₁ h₂ q).spectrum, z.re ≤ s)
    (hβ : s < β) :
    ∃ M > 0, ∀ t : NNReal,
      ‖frontPencilC0Semigroup f D c φ h₁ h₂ q t‖ ≤ M * Real.exp (β * t) := by
  obtain ⟨a, ha, C, _, Ω, _, hsector⟩ :=
    exists_uniform_frontPencil_sectorial_resolvent_bound f D c φ h₁ h₂ (norm_nonneg q)
  let A := frontPencilClosedOperator f D c φ h₁ h₂ q
  let S := frontPencilC0Semigroup f D c φ h₁ h₂ q
  have hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y :=
    frontPencilC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ q
  exact A.exists_semigroup_bound_of_sectorial_spectrum S hgen ha
    (fun z hz ↦ (hsector q le_rfl z hz).2) hspec hβ

/-- Individual decay above every positive real wavenumber cutoff. The decay
rate is common, while the prefactor is allowed to depend on the wavenumber. -/
theorem exists_frontLinearized_pointwise_decay (ψ : ℝ → ℝ^n)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∃ θ > 0, ∀ k : ℝ, k₀ ≤ k → ∃ M > 0, ∀ t : NNReal,
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (k ^ 2) t‖ ≤ M * Real.exp (-θ * t) := by
  obtain ⟨θ, hθ, hgap⟩ := h₃.transverse_high_wavenumber k₀ hk₀
  refine ⟨θ / 2, half_pos hθ, ?_⟩
  intro k hk
  have hspec : ∀ z ∈ (frontPencilClosedOperator f D c φ h₁ h₂ ((k ^ 2 : ℝ) : ℂ)).spectrum,
      z.re ≤ -θ := by
    intro z hz
    apply hgap k hk z
    rw [mem_transverseSpectrum_iff_frontChallengeResolventMap_not_bijective f D c φ h₁ h₂,
      ← frontPencilClosedOperator_resolventMap_eq f D c φ h₁ h₂]
    exact hz
  obtain ⟨M, hM, hMb⟩ := exists_frontPencil_bound_of_spectrum f D c φ h₁ h₂
    ((k ^ 2 : ℝ) : ℂ) hspec (β := -(θ / 2)) (by linarith)
  exact ⟨M, hM, fun t ↦ by
    simpa only [frontLinearizedC0Semigroup_eq_pencil] using hMb t⟩

/-- Uniform real mid/high-frequency decay, combining the compact-annulus
argument with the paper's high-frequency threshold. -/
theorem exists_frontLinearized_midHighFrequency_bound (ψ : ℝ → ℝ^n)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) {k : ℝ} (hk : 0 < k) :
    ∃ M > 0, ∃ μ > 0, ∀ (ξ : ℝ^m) (t : NNReal), k ≤ ‖ξ‖ →
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ‖ ^ 2) t‖ ≤
        M * Real.exp (-μ * t - μ * ‖ξ‖ ^ 2 * t) := by
  obtain ⟨k₁, hk₁, Mh, hMh, μh, hμh, hhigh⟩ :=
    exists_frontLinearized_highFrequency_bound (m := m) f D c φ h₁ h₂
  obtain ⟨θ, hθ, hpoint⟩ := exists_frontLinearized_pointwise_decay f D c φ h₁ h₂ ψ h₃ hk
  obtain ⟨Mm, hMm, hmid⟩ := exists_frontLinearized_midFrequency_bound_of_pointwise
    (m := m) f D c φ h₁ h₂ hk₁ hθ (fun ξ hξ _ ↦ hpoint ‖ξ‖ hξ)
  let μ := min μh (min (θ / 4) (θ / (4 * k₁ ^ 2)))
  have hk₁pos : 0 < k₁ := zero_lt_one.trans_le hk₁
  have hμ : 0 < μ := lt_min hμh (lt_min (by positivity) (by positivity))
  have hμh' : μ ≤ μh := min_le_left _ _
  have hμm₁ : μ ≤ θ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hμm₂ : μ ≤ θ / (4 * k₁ ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨max Mh Mm, hMh.trans_le (le_max_left _ _), μ, hμ, ?_⟩
  intro ξ t hξ
  have hrate {a b : ℝ} (ha : μ ≤ a) (hb : μ ≤ b) :
      -a * (t : ℝ) - b * ‖ξ‖ ^ 2 * t ≤ -μ * t - μ * ‖ξ‖ ^ 2 * t := by gcongr
  by_cases hξ₁ : k₁ ≤ ‖ξ‖
  · exact (hhigh ξ t hξ₁).trans (mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (hrate hμh' hμh')) (Real.exp_pos _).le
      (hMh.le.trans (le_max_left _ _)))
  · exact (hmid ξ t hξ (le_of_not_ge hξ₁)).trans (mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (hrate hμm₁ hμm₂)) (Real.exp_pos _).le
      (hMm.le.trans (le_max_right _ _)))

/-- The operator estimate in Lemma 2.4 at every real frequency above the
prescribed positive cutoff, uniformly over all imaginary contour shifts. -/
theorem exists_frontComplexFrequency_midHighFrequency_bound (ψ : ℝ → ℝ^n)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) {k : ℝ} (hk : 0 < k) :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal), k ≤ ‖ξ₀‖ →
      ‖frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t‖ ≤
        M * Real.exp (-μ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ, hμ, hreal⟩ :=
    exists_frontLinearized_midHighFrequency_bound (m := m) f D c φ h₁ h₂ ψ h₃ hk
  obtain ⟨κ, hκ, hcomplex⟩ :=
    exists_frontComplexFrequency_decay_of_real_bound f D c φ h₁ h₂ hM hμ hreal
  exact ⟨M, hM, μ / 2, half_pos hμ, κ, hκ, hcomplex⟩

/-- Full Lemma 2.4, including the scalar heat multiplier, without the former
high-frequency-only restriction. The cutoff may be any positive number. -/
theorem exists_front_midHighFrequency_bound (ψ : ℝ → ℝ^n)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) {k : ℝ} (hk : 0 < k) :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal), k ≤ ‖ξ₀‖ →
      ‖frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t‖ +
        ‖Complex.exp (-(t * d_perp D φ ψ : ℂ) *
          complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ ≤
        M * Real.exp (-μ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ₁, hμ₁, κ₁, hκ₁, hS⟩ :=
    exists_frontComplexFrequency_midHighFrequency_bound (m := m) f D c φ h₁ h₂ ψ h₃ hk
  let d := d_perp D φ ψ
  have hd : 0 < d := frontTransverseDiffusion_pos f D c φ ψ h₃
  let μ := min μ₁ (min (d * k ^ 2 / 2) (d / 2))
  let κ := max κ₁ d
  have hμ : 0 < μ := lt_min hμ₁ (lt_min (by positivity) (by positivity))
  have hκ : 0 < κ := hκ₁.trans_le (le_max_left _ _)
  refine ⟨M + 1, by positivity, μ, hμ, κ, hκ, ?_⟩
  intro ξ₀ ξ₁ t hξ₀
  have hq : k ^ 2 ≤ ‖ξ₀‖ ^ 2 := pow_le_pow_left₀ hk.le hξ₀ 2
  have hrate {a b e : ℝ} (ha : μ ≤ a) (hb : μ ≤ b) (he : e ≤ κ) :
      -a * (t : ℝ) - b * ‖ξ₀‖ ^ 2 * t + e * ‖ξ₁‖ ^ 2 * t ≤
        -μ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t := by gcongr
  have hS' := (hS ξ₀ ξ₁ t hξ₀).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hrate (min_le_left _ _) (min_le_left _ _) (le_max_left _ _))) hM.le)
  have hheat : ‖Complex.exp (-(t * d_perp D φ ψ : ℂ) *
      complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ ≤
        Real.exp (-(d * k ^ 2 / 2) * t - (d / 2) * ‖ξ₀‖ ^ 2 * t + d * ‖ξ₁‖ ^ 2 * t) := by
    rw [norm_exp_neg_mul_complexFrequencyQuadratic_shift]
    apply Real.exp_le_exp.mpr
    change -(t : ℝ) * d * (‖ξ₀‖ ^ 2 - ‖ξ₁‖ ^ 2) ≤ _
    have hpos : 0 ≤ d * (t : ℝ) * (‖ξ₀‖ ^ 2 - k ^ 2) :=
      mul_nonneg (mul_nonneg hd.le t.2) (sub_nonneg.mpr hq)
    nlinarith only [hpos]
  have hH' := hheat.trans (Real.exp_le_exp.mpr (hrate
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) (le_max_right _ _)))
  simpa only [add_mul, one_mul] using add_le_add hS' hH'

end

end Planarwave
