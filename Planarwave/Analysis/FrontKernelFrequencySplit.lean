/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierContour
import all Planarwave.Analysis.FrontLowFrequencySemigroup
import all Planarwave.Analysis.FrontMidFrequencySemigroup
import Planarwave.Analysis.GaussianFrequencySplit

/-!
# The three frequency contributions to the remainder kernel

Combine Lemmas 2.3 and 2.4 on the low-frequency ball and its complement,
then integrate the high-frequency Gaussian, the exponentially decaying
complementary mode, and the critical Taylor Gaussian separately.
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

local instance : ContinuousENorm (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
  (SeminormedAddGroup.toESeminormedAddMonoid
    (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))).toContinuousENorm

local instance : NormSMulClass ℂ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) := by
  exact NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))

/-- Lemma 2.4 bounds the full remainder outside any prescribed positive cutoff. -/
theorem exists_frontFourierRemainderSymbol_midHigh_bound {k : ℝ} (hk : 0 < k) :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ η : ℝ^m) (t : NNReal), k ≤ ‖ξ‖ →
      ‖frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (complexFrequencyShift ξ η)‖ ≤
        M * Real.exp (-μ * t - μ * ‖ξ‖ ^ 2 * t + κ * ‖η‖ ^ 2 * t) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, hb⟩ :=
    exists_front_midHighFrequency_bound (m := m) f D c φ h₁ h₂ ψ h₃ hk
  let P := profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  refine ⟨M * (‖P‖ + 1), by positivity, μ, hμ, κ, hκ, ?_⟩
  intro ξ η t hξ
  let S := frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ η t
  let a := Complex.exp (-(t * d_perp D φ ψ : ℂ) * complexFrequencyQuadratic (complexFrequencyShift ξ η))
  rw [frontFourierRemainderSymbol, frontFourierSemigroupSymbol_shift]
  calc
    ‖S - a • P‖ ≤ ‖S‖ + ‖a‖ * ‖P‖ := (norm_sub_le _ _).trans_eq (by rw [norm_smul])
    _ ≤ (‖S‖ + ‖a‖) * (‖P‖ + 1) := by
      nlinarith [norm_nonneg S, norm_nonneg a, norm_nonneg P, mul_nonneg (norm_nonneg S) (norm_nonneg P)]
    _ ≤ (M * Real.exp (-μ * t - μ * ‖ξ‖ ^ 2 * t + κ * ‖η‖ ^ 2 * t)) * (‖P‖ + 1) :=
      mul_le_mul_of_nonneg_right (hb ξ η t hξ) (by positivity)
    _ = _ := by ring

/-- Lemma 2.3 splits the low-frequency remainder into its complementary and critical parts. -/
theorem exists_frontFourierRemainderSymbol_low_bound :
    ∃ k > 0, ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ η : ℝ^m) (t : NNReal),
      ‖ξ‖ ≤ k → ‖η‖ ≤ k → 1 ≤ t →
      ‖frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (complexFrequencyShift ξ η)‖ ≤
        M * Real.exp (-μ * t) + (M / t) * Real.exp (-μ * ‖ξ‖ ^ 2 * t + κ * ‖η‖ ^ 2 * t) := by
  obtain ⟨k, hk, M, hM, μ, hμ, κ, hκ, hb⟩ :=
    exists_front_lowFrequency_bound (m := m) f D c φ ψ h₁ h₂ h₃
  refine ⟨k, hk, M, hM, μ, hμ, κ, hκ, ?_⟩
  intro ξ η t hξ hη ht
  obtain ⟨hcomp, htaylor⟩ := hb ξ η t hξ hη ht
  let S := frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ η t
  let P := frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ (complexFrequencyShift ξ η)
  let P₀ := profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)
  let a := Complex.exp (-(t * d_perp D φ ψ : ℂ) * complexFrequencyQuadratic (complexFrequencyShift ξ η))
  have heq : S - a • P₀ = S.comp (ContinuousLinearMap.id ℂ _ - P) + (S.comp P - a • P₀) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    abel
  rw [frontFourierRemainderSymbol, frontFourierSemigroupSymbol_shift]
  change ‖S - a • P₀‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hcomp htaylor)

/-- The paper's integrated `T₁ + T₂ + T₃` estimate, before choosing the small shift. -/
theorem exists_frontShiftedRemainderKernel_threeTerm_bound :
    ∃ k > 0, ∃ M₂ > 0, ∃ μ₂ > 0, ∃ κ₂ > 0, ∃ M₃ > 0, ∃ μ₃ > 0, ∃ κ₃ > 0,
      ∀ (t : NNReal), 1 ≤ t → ∀ η x : ℝ^m, ‖η‖ ≤ k →
      ‖frontShiftedRemainderKernel f D c φ h₁ h₂ ψ h₃ t η x‖ ≤
        Real.exp (-⟪η, x⟫_ℝ) *
          (M₃ * Real.exp (-μ₃ * t + κ₃ * ‖η‖ ^ 2 * t) * (Real.pi / (μ₃ * t)) ^ (m / 2 : ℝ) +
            volume.real (Metric.ball (0 : ℝ^m) k) * (M₂ * Real.exp (-μ₂ * t)) +
            ((M₂ / t) * Real.exp (κ₂ * ‖η‖ ^ 2 * t)) * (Real.pi / (μ₂ * t)) ^ (m / 2 : ℝ)) := by
  obtain ⟨k, hk, M₂, hM₂, μ₂, hμ₂, κ₂, hκ₂, hlow⟩ :=
    exists_frontFourierRemainderSymbol_low_bound (m := m) f D c φ h₁ h₂ ψ h₃
  obtain ⟨M₃, hM₃, μ₃, hμ₃, κ₃, hκ₃, hhigh⟩ :=
    exists_frontFourierRemainderSymbol_midHigh_bound (m := m) f D c φ h₁ h₂ ψ h₃ hk
  refine ⟨k, hk, M₂, hM₂, μ₂, hμ₂, κ₂, hκ₂, M₃, hM₃, μ₃, hμ₃, κ₃, hκ₃, ?_⟩
  intro t ht η x hη
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le (by norm_num) ht
  let g : ℝ^m → (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
    fun ξ ↦ frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (complexFrequencyShift ξ η)
  have hg : Integrable g := by
    have hone (A : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) : (1 : ℂ) • A = A := one_smul ℂ A
    simpa only [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, hone] using!
      integrable_frontFourierRemainderKernel f D c φ h₁ h₂ ψ h₃ t htpos η 0
  have h := norm_oscillatoryIntegral_le_threeTerm (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) hg
    (s := Metric.ball 0 k) measurableSet_ball measure_ball_lt_top.ne
    (A := M₂ * Real.exp (-μ₂ * t))
    (B := (M₂ / t) * Real.exp (κ₂ * ‖η‖ ^ 2 * t))
    (C := M₃ * Real.exp (-μ₃ * t + κ₃ * ‖η‖ ^ 2 * t))
    (b := μ₂ * t) (d := μ₃ * t) (by positivity) (by positivity)
    (mul_pos hμ₂ htpos) (mul_pos hμ₃ htpos) ?_ ?_ x
  · rw [frontShiftedRemainderKernel]
    have hn (a : ℂ) (A : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) : ‖a • A‖ = ‖a‖ * ‖A‖ := norm_smul a A
    rw [hn, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    simpa only [finrank_euclideanSpace_fin] using!
      mul_le_mul_of_nonneg_left h (Real.exp_pos (-⟪η, x⟫_ℝ)).le
  · intro ξ hξ
    have hξ' : k ≤ ‖ξ‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hξ
    apply (hhigh ξ η t hξ').trans_eq
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · intro ξ hξ
    have hξ' : ‖ξ‖ ≤ k := (by simpa only [Metric.mem_ball, dist_zero_right] using hξ : ‖ξ‖ < k).le
    apply (hlow ξ η t hξ' hη ht).trans_eq
    congr 1
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring

end

end Planarwave
