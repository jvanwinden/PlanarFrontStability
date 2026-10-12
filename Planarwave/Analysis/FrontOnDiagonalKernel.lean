/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontKernelFrequencySplit
import Planarwave.Analysis.GaussianKernelDecay

/-!
# On-diagonal remainder kernel estimate

This follows the three-term proof of the on-diagonal proposition in Section 3.
The contour offset is `η = ε x/t`. A single small positive `ε` keeps the offset
inside the low-frequency box, preserves high-frequency exponential decay, and
absorbs the critical-mode imaginary growth into half the spatial Gaussian.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The paper's on-diagonal proposition, in operator norm, for any fixed positive
spatial threshold. The exponent `m/2 + 1` is `(d+1)/2` when `m = d-1`. -/
theorem exists_frontRemainderKernel_onDiagonal_bound {R : ℝ} (hR : 0 < R) :
    ∃ C > 0, ∃ ν > 0, ∀ (t : NNReal), 1 ≤ t → ∀ x : ℝ^m,
      ‖x‖ / t ≤ R →
      ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x‖ ≤
        C * (t : ℝ) ^ (-(m / 2 + 1 : ℝ)) * Real.exp (-ν * ‖x‖ ^ 2 / t) := by
  obtain ⟨k, hk, M₂, hM₂, μ₂, hμ₂, κ₂, hκ₂, M₃, hM₃, μ₃, hμ₃, κ₃, hκ₃, hb⟩ :=
    exists_frontShiftedRemainderKernel_threeTerm_bound (m := m) f D c φ h₁ h₂ ψ h₃
  obtain ⟨ε, hε, hek, heμ, heκ⟩ := exists_onDiagonal_small_shift hk hR hμ₃ hκ₃ hκ₂
  let p : ℝ := m / 2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  obtain ⟨C₁, hC₁, htime₁⟩ := exists_exp_neg_mul_le_rpow (half_pos hμ₃) (p + 1)
  obtain ⟨C₂, hC₂, htime₂⟩ := exists_exp_neg_mul_le_rpow hμ₂ (p + 1)
  let v := volume.real (Metric.ball (0 : ℝ^m) k)
  have hv : 0 ≤ v := measureReal_nonneg
  let A₁ := M₃ * (Real.pi / μ₃) ^ p * C₁
  let A₂ := v * M₂ * C₂
  let A₃ := M₂ * (Real.pi / μ₂) ^ p
  have hA₁ : 0 < A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hA₃ : 0 < A₃ := by dsimp [A₃]; positivity
  refine ⟨A₁ + A₂ + A₃, by positivity, ε / 2, half_pos hε, ?_⟩
  intro t ht x hx
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht
  let η := (ε / (t : ℝ)) • x
  have hη : ‖η‖ ≤ ε * R := norm_onDiagonal_shift_le hε.le htpos x hx
  have hηk : ‖η‖ ≤ k := hη.trans hek
  have hhigh : -μ₃ * t + κ₃ * ‖η‖ ^ 2 * t ≤ -(μ₃ / 2) * t := by
    have hs := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg η) hη 2) hκ₃.le).trans heμ
    have hh := mul_le_mul_of_nonneg_right hs htpos.le
    linarith
  let E := Real.exp (-(ε / 2) * ‖x‖ ^ 2 / t)
  let T := (t : ℝ) ^ (-(p + 1))
  have hE : 0 < E := Real.exp_pos _
  have hT : 0 < T := Real.rpow_pos_of_pos htpos _
  have houter : Real.exp (-⟪η, x⟫_ℝ) ≤ E := by
    apply Real.exp_le_exp.mpr
    simpa only [zero_mul, add_zero] using
      onDiagonal_shift_exponent_le (κ := 0) hε.le htpos (by norm_num) x
  have hcritical : Real.exp (-⟪η, x⟫_ℝ + κ₂ * ‖η‖ ^ 2 * t) ≤ E :=
    Real.exp_le_exp.mpr (onDiagonal_shift_exponent_le hε.le htpos heκ x)
  -- T₁: high frequencies retain exponential decay after the small shift.
  have h₁term : Real.exp (-⟪η, x⟫_ℝ) *
      (M₃ * Real.exp (-μ₃ * t + κ₃ * ‖η‖ ^ 2 * t) * (Real.pi / (μ₃ * t)) ^ p) ≤
      A₁ * T * E := by
    have hexp : Real.exp (-μ₃ * t + κ₃ * ‖η‖ ^ 2 * t) ≤ C₁ * T :=
      (Real.exp_le_exp.mpr hhigh).trans (htime₁ t ht)
    calc
      _ ≤ E * (M₃ * (C₁ * T) * (Real.pi / μ₃) ^ p) := by
        apply mul_le_mul houter _ (by positivity) hE.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hM₃.le)
          (gaussian_mass_le hμ₃ ht hp) (by positivity) (by positivity)
      _ = _ := by dsimp [A₁]; ring
  -- T₂: the low-frequency complement has uniform exponential decay.
  have h₂term : Real.exp (-⟪η, x⟫_ℝ) * (v * (M₂ * Real.exp (-μ₂ * t))) ≤ A₂ * T * E := by
    calc
      _ ≤ E * (v * (M₂ * (C₂ * T))) := by
        apply mul_le_mul houter _ (by positivity) hE.le
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (htime₂ t ht) hM₂.le) hv
      _ = _ := by dsimp [A₂]; ring
  -- T₃: integrate the Taylor Gaussian and absorb its imaginary growth.
  have h₃term : Real.exp (-⟪η, x⟫_ℝ) *
      (((M₂ / t) * Real.exp (κ₂ * ‖η‖ ^ 2 * t)) * (Real.pi / (μ₂ * t)) ^ p) ≤
      A₃ * T * E := by
    calc
      _ = ((M₂ / t) * (Real.pi / (μ₂ * t)) ^ p) *
          Real.exp (-⟪η, x⟫_ℝ + κ₂ * ‖η‖ ^ 2 * t) := by rw [Real.exp_add]; ring
      _ ≤ ((M₂ / t) * (Real.pi / (μ₂ * t)) ^ p) * E := by
        exact mul_le_mul_of_nonneg_left hcritical (by positivity)
      _ = _ := by rw [critical_gaussian_mass_scaling hμ₂ htpos]
  have h := hb t ht η x hηk
  rw [frontShiftedRemainderKernel_eq f D c φ h₁ h₂ ψ h₃ t htpos] at h
  apply h.trans
  change Real.exp (-⟪η, x⟫_ℝ) * (_ + _ + _) ≤ (A₁ + A₂ + A₃) * T * E
  rw [mul_add, mul_add]
  exact (add_le_add (add_le_add h₁term h₂term) h₃term).trans_eq (by ring)

/-- The pointwise version of the on-diagonal estimate for longitudinal slices. -/
theorem exists_frontRemainderKernel_onDiagonal_pointwise_bound {R : ℝ} (hR : 0 < R) :
    ∃ C > 0, ∃ ν > 0, ∀ (t : NNReal), 1 ≤ t → ∀ x : ℝ^m,
      ‖x‖ / t ≤ R → ∀ (v : BUC ℝ (ℂ^n)) (z : ℝ),
      ‖frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x v z‖ ≤
        C * (t : ℝ) ^ (-(m / 2 + 1 : ℝ)) * Real.exp (-ν * ‖x‖ ^ 2 / t) * ‖v‖ := by
  obtain ⟨C, hC, ν, hν, hb⟩ :=
    exists_frontRemainderKernel_onDiagonal_bound (m := m) f D c φ h₁ h₂ ψ h₃ hR
  refine ⟨C, hC, ν, hν, ?_⟩
  intro t ht x hx v z
  exact (BUC.norm_apply_le _ z).trans
    (((frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb t ht x hx) (norm_nonneg v)))

end

end Planarwave
