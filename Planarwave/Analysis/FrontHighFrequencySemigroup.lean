/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAllFrequencySemigroup

/-!
# High-frequency longitudinal semigroup decay

The high-frequency step of Lemma 2.4 chooses `k₁ = sqrt (2 C / μ₀ + 1)` in (2.3), giving
decay both in time and in the real frequency. The same bounded contour perturbation used in
Lemma 2.2 then extends that decay to imaginary frequencies. The intermediate-frequency range
below this threshold is handled separately in `FrontMidFrequencySemigroup`, using the
analytic-semigroup spectral-to-growth theorem and compact-family uniformization.
-/

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- The real high-frequency estimate (2.8), with the threshold chosen as in the paper. -/
theorem exists_frontLinearized_highFrequency_bound :
    ∃ k₁ : ℝ, 1 ≤ k₁ ∧ ∃ M > 0, ∃ μ > 0,
      ∀ (ξ₀ : ℝ^m) (t : NNReal), k₁ ≤ ‖ξ₀‖ →
        ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ₀‖ ^ 2) t‖ ≤
          M * Real.exp (-μ * t - μ * ‖ξ₀‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ₀, hμ₀, C, hC, hbound⟩ := exists_uniform_frontLinearized_bound f D c φ h₁ h₂
  let Q := 2 * C / μ₀ + 1
  have hQ : 1 ≤ Q := by
    have hnonneg : 0 ≤ 2 * C / μ₀ := by positivity
    dsimp [Q]
    linarith
  have hsqrt : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt (zero_le_one.trans hQ)
  have hroot : 1 ≤ Real.sqrt Q := by nlinarith [Real.sqrt_nonneg Q]
  refine ⟨Real.sqrt Q, hroot, M, hM, μ₀ / 2, by positivity, ?_⟩
  intro ξ₀ t hξ₀
  have hq : Q ≤ ‖ξ₀‖ ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg Q) hξ₀ 2
    rwa [hsqrt] at h
  have hCQ : μ₀ * Q = 2 * C + μ₀ := by dsimp [Q]; field_simp
  have hrate : C - μ₀ * ‖ξ₀‖ ^ 2 ≤ -μ₀ / 2 - (μ₀ / 2) * ‖ξ₀‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hq hμ₀.le]
  apply (hbound (‖ξ₀‖ ^ 2) (sq_nonneg _) t).trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hrate t.2]

/-- The final bounded-perturbation step of Lemma 2.4. A real-frequency decay estimate extends
to the shifted contour, with half the Gaussian decay retained. This is also applicable to the
combined mid- and high-frequency real estimate once the mid-frequency bound is available. -/
theorem exists_frontComplexFrequency_decay_of_real_bound {k M μ : ℝ}
    (hM : 0 < M) (hμ : 0 < μ)
    (hreal : ∀ (ξ₀ : ℝ^m) (t : NNReal), k ≤ ‖ξ₀‖ →
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ₀‖ ^ 2) t‖ ≤
        M * Real.exp (-μ * t - μ * ‖ξ₀‖ ^ 2 * t)) :
    ∃ κ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal), k ≤ ‖ξ₀‖ →
      ‖frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t‖ ≤
        M * Real.exp (-(μ / 2) * t - (μ / 2) * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  let K := M * ‖frontComplexifiedDiffusionBUC D‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ := μ / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (2 * (K + 1)) = μ := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hδsmall : K * δ ≤ μ / 2 := by nlinarith
  let κ := K * (1 + δ⁻¹) + 1
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hKκ : K * (1 + δ⁻¹) ≤ κ := by dsimp [κ]; linarith
  refine ⟨κ, hκ, ?_⟩
  intro ξ₀ ξ₁ t hξ₀
  let B := frontComplexFrequencyBoundedPerturbation D ξ₀ ξ₁
  have hpert : M * ‖B‖ ≤ K * δ * ‖ξ₀‖ ^ 2 + K * (1 + δ⁻¹) * ‖ξ₁‖ ^ 2 := by
    calc
      M * ‖B‖ ≤ M * ((δ * ‖ξ₀‖ ^ 2 + (1 + δ⁻¹) * ‖ξ₁‖ ^ 2) *
          ‖frontComplexifiedDiffusionBUC D‖) :=
        mul_le_mul_of_nonneg_left
          (norm_frontComplexFrequencyBoundedPerturbation_le_young D ξ₀ ξ₁ hδ) hM.le
      _ = _ := by dsimp [K]; ring
  have hrate : -μ - μ * ‖ξ₀‖ ^ 2 + M * ‖B‖ ≤
      -(μ / 2) - (μ / 2) * ‖ξ₀‖ ^ 2 + κ * ‖ξ₁‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδsmall) (sq_nonneg ‖ξ₀‖),
      mul_nonneg (sub_nonneg.mpr hKκ) (sq_nonneg ‖ξ₁‖)]
  have hfree : ∀ r : NNReal,
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ₀‖ ^ 2) r‖ ≤
        M * Real.exp ((-μ - μ * ‖ξ₀‖ ^ 2) * r) := by
    intro r
    simpa only [sub_mul] using! hreal ξ₀ r hξ₀
  have h := (frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ₀‖ ^ 2)).norm_boundedPerturbation_le
    B hM.le hfree t
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  simpa only [add_mul, sub_mul] using! mul_le_mul_of_nonneg_right hrate t.2

/-- The operator part of Lemma 2.4 for all real frequencies above the high-frequency threshold,
uniformly in the imaginary contour frequency. -/
theorem exists_frontComplexFrequency_highFrequency_bound :
    ∃ k₁ : ℝ, 1 ≤ k₁ ∧ ∃ M > 0, ∃ μ > 0, ∃ κ > 0,
      ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal), k₁ ≤ ‖ξ₀‖ →
        ‖frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t‖ ≤
          M * Real.exp (-μ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨k₁, hk₁, M, hM, μ, hμ, hreal⟩ :=
    exists_frontLinearized_highFrequency_bound (m := m) f D c φ h₁ h₂
  obtain ⟨κ, hκ, hcomplex⟩ :=
    exists_frontComplexFrequency_decay_of_real_bound f D c φ h₁ h₂ hM hμ hreal
  exact ⟨k₁, hk₁, M, hM, μ / 2, half_pos hμ, κ, hκ, hcomplex⟩

/-- The full estimate of Lemma 2.4 above the high-frequency threshold, including the scalar
heat multiplier. The intermediate-frequency interval is handled in `FrontMidFrequencySemigroup`. -/
theorem exists_front_highFrequency_bound (ψ : ℝ → ℝ^n)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
    ∃ k₁ : ℝ, 1 ≤ k₁ ∧ ∃ M > 0, ∃ μ > 0, ∃ κ > 0,
      ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal), k₁ ≤ ‖ξ₀‖ →
        ‖frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t‖ +
          ‖Complex.exp (-(t * d_perp D φ ψ : ℂ) *
            complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ ≤
          M * Real.exp (-μ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨k₁, hk₁, M, hM, μ₁, hμ₁, κ₁, hκ₁, hS⟩ :=
    exists_frontComplexFrequency_highFrequency_bound (m := m) f D c φ h₁ h₂
  let d := d_perp D φ ψ
  have hd : 0 < d := frontTransverseDiffusion_pos f D c φ ψ h₃
  let μ := min μ₁ (d / 2)
  let κ := max κ₁ d
  have hμ : 0 < μ := lt_min hμ₁ (half_pos hd)
  have hκ : 0 < κ := hκ₁.trans_le (le_max_left _ _)
  refine ⟨k₁, hk₁, M + 1, by positivity, μ, hμ, κ, hκ, ?_⟩
  intro ξ₀ ξ₁ t hξ₀
  have hq : 1 ≤ ‖ξ₀‖ ^ 2 := by nlinarith [hk₁.trans hξ₀]
  have hrate {a b : ℝ} (ha : μ ≤ a) (hb : b ≤ κ) :
      -a * (t : ℝ) - a * ‖ξ₀‖ ^ 2 * t + b * ‖ξ₁‖ ^ 2 * t ≤
        -μ * t - μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t := by
    gcongr
  have hS' := (hS ξ₀ ξ₁ t hξ₀).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (hrate (min_le_left _ _) (le_max_left _ _))) hM.le)
  have hheat : ‖Complex.exp (-(t * d_perp D φ ψ : ℂ) *
      complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))‖ ≤
        Real.exp (-(d / 2) * t - (d / 2) * ‖ξ₀‖ ^ 2 * t + d * ‖ξ₁‖ ^ 2 * t) := by
    rw [norm_exp_neg_mul_complexFrequencyQuadratic_shift]
    apply Real.exp_le_exp.mpr
    change -(t : ℝ) * d * (‖ξ₀‖ ^ 2 - ‖ξ₁‖ ^ 2) ≤ _
    have hpos : 0 ≤ d * (t : ℝ) * (‖ξ₀‖ ^ 2 - 1) :=
      mul_nonneg (mul_nonneg hd.le t.2) (sub_nonneg.mpr hq)
    nlinarith only [hpos]
  have hH' := hheat.trans (Real.exp_le_exp.mpr (hrate (min_le_right _ _) (le_max_right _ _)))
  simpa only [add_mul, one_mul] using add_le_add hS' hH'

end

end Planarwave
