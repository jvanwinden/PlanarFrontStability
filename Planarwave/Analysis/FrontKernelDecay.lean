/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontOnDiagonalKernel
import all Planarwave.Analysis.FrontOffDiagonalKernel

/-!
# Spatially integrated remainder kernel decay

Combine the on- and off-diagonal estimates at their common spatial threshold,
as in the proof of the decomposition theorem in Section 3. The resulting
Gaussian has mass of order `t^(m/2)`, leaving the required `1/t` decay.
This file proves estimates for the actual Fourier kernel; identifying its
convolution with the full spatial semigroup is a separate obligation.
-/

open MeasureTheory

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  (SeminormedAddGroup.toESeminormedAddMonoid
    (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))).toContinuousENorm

/-- The common Gaussian majorant obtained by combining the two spatial regions. -/
theorem exists_frontRemainderKernel_gaussianDecay_bound :
    ∃ C > 0, ∃ ν > 0, ∀ (t : NNReal), 1 ≤ t → ∀ x : ℝ^m,
      ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ ≤
        C * (t : ℝ) ^ (-(m / 2 + 1 : ℝ)) * Real.exp (-ν * ‖x‖ ^ 2 / t) := by
  obtain ⟨C₁, hC₁, R, hR, ν₁, hν₁, hoff⟩ :=
    exists_frontRemainderKernel_offDiagonal_bound (m := m) f D c φ h₁ h₂ ψ h₃
  obtain ⟨C₂, hC₂, ν₂, hν₂, hon⟩ :=
    exists_frontRemainderKernel_onDiagonal_bound (m := m) f D c φ h₁ h₂ ψ h₃ hR
  obtain ⟨B, hB, htime⟩ := exists_exp_neg_mul_le_rpow hν₁ (m / 2 + 1 : ℝ)
  let ν := min ν₁ ν₂
  refine ⟨C₁ * B + C₂, by positivity, ν, lt_min hν₁ hν₂, ?_⟩
  intro t ht x
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht
  have hgauss {a : ℝ} (ha : ν ≤ a) :
      Real.exp (-a * ‖x‖ ^ 2 / t) ≤ Real.exp (-ν * ‖x‖ ^ 2 / t) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (neg_le_neg ha) (sq_nonneg _)) htpos.le
  rcases le_total (‖x‖ / (t : ℝ)) R with hx | hx
  · apply (hon t ht x hx).trans
    apply mul_le_mul _ (hgauss (min_le_right _ _)) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg htpos.le _)
  · calc
      _ ≤ C₁ * Real.exp (-ν₁ * t - ν₁ * ‖x‖ ^ 2 / t) := hoff t ht x hx
      _ = (C₁ * Real.exp (-ν₁ * t)) * Real.exp (-ν₁ * ‖x‖ ^ 2 / t) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ (C₁ * (B * (t : ℝ) ^ (-(m / 2 + 1 : ℝ)))) * Real.exp (-ν * ‖x‖ ^ 2 / t) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (htime t ht) hC₁.le)
          (hgauss (min_le_left _ _)) (by positivity) (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc C₁ B]
        gcongr
        exact le_add_of_nonneg_right hC₂.le

/-- The spatial `L¹` norm of the unnormalized Fourier remainder kernel is `O(1/t)`.
All constants depend only on the fixed front, not on time or the perturbation. -/
theorem exists_frontRemainderKernel_integral_norm_bound :
    ∃ C > 0, ∀ (t : NNReal), 1 ≤ t →
      (∫ x : ℝ^m, ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖) ≤ C / t := by
  obtain ⟨C, hC, ν, hν, hb⟩ :=
    exists_frontRemainderKernel_gaussianDecay_bound (m := m) f D c φ h₁ h₂ ψ h₃
  let p : ℝ := m / 2
  refine ⟨C * (Real.pi / ν) ^ p, by positivity, ?_⟩
  intro t ht
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht
  have hbt : 0 < ν / (t : ℝ) := div_pos hν htpos
  have hbound (x : ℝ^m) : ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ ≤
      (C * (t : ℝ) ^ (-(p + 1))) * Real.exp (-(ν / t) * ‖x‖ ^ 2) := by
    apply (hb t ht x).trans_eq
    congr 2
    ring
  calc
    _ ≤ ∫ x : ℝ^m, (C * (t : ℝ) ^ (-(p + 1))) * Real.exp (-(ν / t) * ‖x‖ ^ 2) := by
      apply integral_mono _ ((integrable_gaussian_norm hbt).const_mul _) hbound
      exact Integrable.norm (β := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
        (integrable_frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t htpos)
    _ = (C * (t : ℝ) ^ (-(p + 1))) * (Real.pi / (ν / t)) ^ p := by
      rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hbt,
        finrank_euclideanSpace_fin]
    _ = (C * (Real.pi / ν) ^ p) / t := by
      rw [show Real.pi / (ν / (t : ℝ)) = (Real.pi / ν) * t by field_simp,
        Real.mul_rpow (by positivity) htpos.le]
      calc
        _ = C * (Real.pi / ν) ^ p * ((t : ℝ) ^ (-(p + 1)) * (t : ℝ) ^ p) := by ring
        _ = _ := by rw [← Real.rpow_add htpos]; ring_nf; simp [Real.rpow_neg_one]

end

end Planarwave
