/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontRealProfileDerivatives
import all Planarwave.Analysis.FrontNonlinearity
import Planarwave.Analysis.PositiveDiffusion
import Planarwave.Analysis.BUCAutonomousODEBounds
import Planarwave.Analysis.ModulationHigherBounds

/-!
# Uniform higher bounds for the fixed front profile

The bounded phase-space trajectory `(φ, φ')` solves the smooth autonomous
traveling-wave ODE. Its compact state range and repeated differentiation
give BUC derivatives of every order. In particular, subtracting the fixed
profile in Step 4 does not require an additional `C^9` assumption.
-/

open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ ψ : ℝ → ℝ^n)
  (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₁ h₃ in
set_option maxHeartbeats 800000 in
/-- All spatial derivatives of the actual split-coordinate front are
bounded and uniformly continuous, derived from the original hypotheses. -/
theorem exists_frontSplitProfile_cn_bound (k : ℕ) :
    ∃ P > 0, BUCSpatialBound k (frontSplitProfileBUC (m := m) f D c φ h₂) P := by
  let p : BUC ℝ (ℝ^n) := BUC.ofTwoEnded h₂.smooth.continuous
    (tendsto_frontLeftState f D c φ h₂) (tendsto_frontRightState f D c φ h₂)
  let q := realTranslationModeBUC f D c φ ψ h₃
  let w : BUC ℝ (ℝ^n × ℝ^n) :=
    BUC.postcompCLM (ContinuousLinearMap.inl ℝ (ℝ^n) (ℝ^n)) p +
      BUC.postcompCLM (ContinuousLinearMap.inr ℝ (ℝ^n) (ℝ^n)) q
  have hw (z : ℝ) : w z = (φ z, deriv φ z) := by
    simp only [w, p, q, BUC.add_apply, BUC.postcompCLM_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
      realTranslationModeBUC_apply, Prod.mk_add_mk, add_zero, zero_add]
    rfl
  let J : (ℝ^n) ≃L[ℝ] (ℝ^n) :=
    (LinearEquiv.ofBijective D.toLinearMap
      (bijective_of_positive_injective D h₁.positive h₁.kernel)).toContinuousLinearEquiv
  let R : (ℝ^n × ℝ^n) → (ℝ^n × ℝ^n) :=
    fun v ↦ (v.2, J.symm (-(c • v.2 + f v.1)))
  have hR : ContDiff ℝ ∞ R := contDiff_snd.prodMk
    (J.symm.contDiff.comp (((contDiff_snd.const_smul c).add (h₁.smooth.comp contDiff_fst)).neg))
  have hsecond (z : ℝ) : deriv (deriv φ) z = J.symm (-(c • deriv φ z + f (φ z))) := by
    have hode : D (deriv (deriv φ) z) + (c • deriv φ z + f (φ z)) = 0 := by
      simpa only [InnerProductSpace.laplacian_eq_iteratedDeriv_real,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
        iteratedDeriv_zero, add_assoc] using h₂.ode z
    have heq : J (deriv (deriv φ) z) = -(c • deriv φ z + f (φ z)) := eq_neg_of_add_eq_zero_left hode
    rw [← heq, J.symm_apply_apply]
  have hd : ∀ z, HasDerivAt w (R (w z)) z := by
    intro z
    have hφ := (h₂.smooth.differentiable (by simp) z).hasDerivAt
    have hφ' := ((contDiff_infty_iff_deriv.mp h₂.smooth).2.differentiable (by simp) z).hasDerivAt
    have hwfun : (w : ℝ → ℝ^n × ℝ^n) = fun r ↦ (φ r, deriv φ r) := funext hw
    rw [hwfun]
    change HasDerivAt (fun r ↦ (φ r, deriv φ r))
      (deriv φ z, J.symm (-(c • deriv φ z + f (φ z)))) z
    rw [← hsecond z]
    exact hφ.prodMk hφ'
  obtain ⟨A, hA, hb⟩ := exists_bucSpatialBound_observable_of_ode w R hR hd k
    (Prod.fst : (ℝ^n × ℝ^n) → ℝ^n) contDiff_fst
  have heq : BUC.postcompContinuous Prod.fst continuous_fst w = p := by
    ext z
    simp only [BUC.postcompContinuous_apply, hw]
    rfl
  rw [heq] at hb
  have hs := hb.precomp_contraction (ContinuousLinearMap.snd ℝ (ℝ^m) ℝ)
    (ContinuousLinearMap.norm_snd_le ℝ (ℝ^m) ℝ)
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  exact hs.mono (le_max_left _ _)

end

end Planarwave
