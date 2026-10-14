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

end

end Planarwave
