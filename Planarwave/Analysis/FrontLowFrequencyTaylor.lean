/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontCriticalSemigroup
import Planarwave.Analysis.SpectralTaylorEstimate

/-!
# The low-frequency critical-mode Taylor estimate

This proves the second estimate in Lemma 2.3. We use the exact critical semigroup identity,
the fourth-order eigenvalue and second-order projection expansions, and the paper's absorption
of the polynomial prefactor into a weaker Gaussian. The complementary spectral-subspace
estimate is separate and still requires the analytic-semigroup spectral bound theorem.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-- The squared norm on the shifted contour is the sum of the two real squared norms. -/
theorem norm_complexFrequencyShift_sq {m : ℕ} (ξ₀ ξ₁ : ℝ^m) :
    ‖complexFrequencyShift ξ₀ ξ₁‖ ^ 2 = ‖ξ₀‖ ^ 2 + ‖ξ₁‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [complexFrequencyShift_apply, Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

/-- A convenient radius estimate for choosing the compact contour box inside the Taylor
neighborhood. -/
theorem norm_complexFrequencyShift_le {m : ℕ} (ξ₀ ξ₁ : ℝ^m) :
    ‖complexFrequencyShift ξ₀ ξ₁‖ ≤ ‖ξ₀‖ + ‖ξ₁‖ := by
  calc
    ‖complexFrequencyShift ξ₀ ξ₁‖ ≤ ‖embed ξ₀‖ + ‖Complex.I • embed ξ₁‖ := norm_add_le _ _
    _ = ‖ξ₀‖ + ‖ξ₁‖ := by simp [norm_smul, norm_embed]

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) [Nontrivial (ℝ^n)]

/-- The second bound of Lemma 2.3: the critical semigroup differs from the transverse heat
multiplier by `O(t⁻¹)`, uniformly on a sufficiently small complex contour box. -/
theorem exists_frontCriticalSemigroup_taylor_bound :
    ∃ k > 0, ∃ M > 0, ∃ μ > 0, ∃ κ > 0,
      ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal), ‖ξ₀‖ ≤ k → ‖ξ₁‖ ≤ k → 1 ≤ t →
        ‖(frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t).comp
              (frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃
                (complexFrequencyShift ξ₀ ξ₁)) -
            Complex.exp (-(t * d_perp D φ ψ : ℂ) *
                complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)) •
              profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)‖ ≤
          (M / t) * Real.exp (-μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  let d := d_perp D φ ψ
  have hd : 0 < d := frontTransverseDiffusion_pos f D c φ ψ h₃
  let P₀ : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  obtain ⟨C, hC, hTaylor⟩ :=
    exists_frontCriticalExpansion_complexFrequency_bound (m := m) f D c φ ψ h₁ h₂ h₃
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (hTaylor.and (eventually_frontCriticalSemigroup_eq (m := m) f D c φ ψ h₁ h₂ h₃))
  let k := min (ε / 4) (min (1 / 2) (Real.sqrt (d / (4 * C))))
  have hk : 0 < k := by dsimp [k]; positivity
  have hkε : k ≤ ε / 4 := min_le_left _ _
  have hk1 : k ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hkroot : k ≤ Real.sqrt (d / (4 * C)) := (min_le_right _ _).trans (min_le_right _ _)
  have hk2 : k ^ 2 ≤ d / (4 * C) := by
    have h := pow_le_pow_left₀ hk.le hkroot 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have hkC : C * (2 * k ^ 2) ≤ d / 2 := by
    have h := mul_le_mul_of_nonneg_left hk2 (show 0 ≤ 4 * C by positivity)
    rw [mul_div_cancel₀ _ (show 4 * C ≠ 0 by positivity)] at h
    nlinarith
  let K := ‖P₀‖ + C
  have hK : 0 < K := by dsimp [K]; positivity
  let L := (d / 4)⁻¹ + 2 * ((d / 4)⁻¹) ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨k, hk, C * (K + 1) * L, by positivity, d / 4, by positivity,
    2 * d, by positivity, ?_⟩
  intro ξ₀ ξ₁ t hξ₀ hξ₁ ht
  have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht
  let ξ := complexFrequencyShift ξ₀ ξ₁
  have hξ : ‖ξ‖ ≤ 2 * k := (norm_complexFrequencyShift_le ξ₀ ξ₁).trans (by linarith)
  have hξ1 : ‖ξ‖ ≤ 1 := by linarith
  have hξε : dist ξ 0 < ε := by rw [dist_zero_right]; linarith
  obtain ⟨⟨hz, hP₀⟩, hsemigroup⟩ := hlocal hξε
  let P : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ
  let z := frontCriticalEigenvalueAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ
  let w := -(d : ℂ) * complexFrequencyQuadratic ξ
  change ‖P - P₀‖ ≤ C * ‖ξ‖ ^ 2 at hP₀
  have hzw : ‖z - w‖ ≤ C * ‖ξ‖ ^ 4 := by simpa only [z, w, sub_neg_eq_add, neg_mul] using hz
  have hP : ‖P‖ ≤ K := by
    calc
      ‖P‖ ≤ ‖P - P₀‖ + ‖P₀‖ := norm_le_norm_sub_add P P₀
      _ ≤ C * ‖ξ‖ ^ 2 + ‖P₀‖ := by linarith
      _ ≤ C * 1 ^ 2 + ‖P₀‖ := by gcongr
      _ = K := by dsimp [K]; ring
  have hsq : ‖ξ‖ ^ 2 = ‖ξ₀‖ ^ 2 + ‖ξ₁‖ ^ 2 := norm_complexFrequencyShift_sq ξ₀ ξ₁
  have hfour : ‖ξ‖ ^ 4 = (‖ξ₀‖ ^ 2 + ‖ξ₁‖ ^ 2) ^ 2 := by rw [← hsq]; ring
  have hw : w.re = -d * (‖ξ₀‖ ^ 2 - ‖ξ₁‖ ^ 2) := by
    dsimp [w, ξ]
    simp [Complex.mul_re, complexFrequencyQuadratic_shift_re]
  have hsmall : C * (‖ξ₀‖ ^ 2 + ‖ξ₁‖ ^ 2) ≤ d / 2 := by
    apply le_trans _ hkC
    apply mul_le_mul_of_nonneg_left _ hC.le
    nlinarith [pow_le_pow_left₀ (norm_nonneg ξ₀) hξ₀ 2,
      pow_le_pow_left₀ (norm_nonneg ξ₁) hξ₁ 2]
  have hrough := norm_exp_smul_sub_exp_smul_le_taylor P P₀ z w (t := (t : ℝ)) t.2 (norm_nonneg ξ)
    hC.le hK.le hzw hP hP₀
  have habsorb := polynomial_gaussian_absorption hd (sq_nonneg ‖ξ₀‖) (sq_nonneg ‖ξ₁‖) ht0 hsmall
  rw [hsq, hfour, hw] at hrough
  have hexponent : (t : ℝ) * (-d * (‖ξ₀‖ ^ 2 - ‖ξ₁‖ ^ 2)) +
      C * (‖ξ₀‖ ^ 2 + ‖ξ₁‖ ^ 2) ^ 2 * t =
      -d * ‖ξ₀‖ ^ 2 * t + d * ‖ξ₁‖ ^ 2 * t + C * (‖ξ₀‖ ^ 2 + ‖ξ₁‖ ^ 2) ^ 2 * t := by ring
  rw [hexponent] at hrough
  have hfinal := hrough.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left habsorb
      (show 0 ≤ C * (K + 1) by positivity))
  rw [hsemigroup ξ₀ ξ₁ rfl t]
  have htw : (t : ℂ) * w = -(t * d_perp D φ ψ : ℂ) * complexFrequencyQuadratic ξ := by
    dsimp [w, d]; ring
  simpa only [htw, P, P₀, z, ξ, div_eq_mul_inv, mul_assoc] using! hfinal

end

end Planarwave
