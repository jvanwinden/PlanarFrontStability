/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontComplementSemigroup
import all Planarwave.Analysis.FrontLowFrequencyTaylor
import Planarwave.Analysis.SemigroupCompactSpectralBounds

/-!
# Uniform low-frequency semigroup estimates

Following Lemma 2.3, restrict to the noncritical spectral subspace, use its
individual decay rate `-θ/4`, and apply the appendix's compact-family lemma with
rate loss `θ/8`. The complementary projections depend on frequency; the fixed-space
extension in `SemigroupCompactSpectralBounds` handles this dependence explicitly.
Finally choose one contour box and common constants for this estimate and the
critical-mode Taylor estimate.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) [Nontrivial (ℝ^n)]

/-- The paper's `-θ/4` individual bounds become one uniform `-θ/8` bound on a
closed neighborhood of the analytic pencil parameter. -/
theorem exists_frontPencil_uniform_complement_bound :
    ∃ r > 0, ∃ M > 0, ∃ θ > 0, ∀ q : ℂ, ‖q‖ ≤ r → ∀ t : NNReal,
      ‖(frontPencilC0Semigroup f D c φ h₁ h₂ q t).comp
          (ContinuousLinearMap.id ℂ (BUC ℝ (ℂ^n)) -
            frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q)‖ ≤
        M * Real.exp (-(θ / 8) * t) := by
  let P := frontCriticalProjection f D c φ ψ h₁ h₂ h₃
  let ζ := frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃
  obtain ⟨θ, hθ, hpoint⟩ := exists_eventually_frontPencil_complement_bound f D c φ ψ h₁ h₂ h₃
  obtain ⟨UP, hUP, hPc⟩ := (contDiffAt_frontCriticalProjection f D c φ ψ h₁ h₂ h₃).contDiffOn
    (m := 0) bot_le (by simp)
  obtain ⟨UZ, hUZ, hζc⟩ := (contDiffAt_frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃).contDiffOn
    (m := 0) bot_le (by simp)
  have hlocal := hpoint.and
    ((eventually_frontCriticalProjection_idempotent f D c φ ψ h₁ h₂ h₃).and
      ((eventually_frontPencilSemigroup_comp_criticalProjection f D c φ ψ h₁ h₂ h₃).and
        ((eventually_frontCriticalProjection_eigenrange f D c φ ψ h₁ h₂ h₃).and
          (Filter.Eventually.and hUP hUZ))))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  let K := Metric.closedBall (0 : ℂ) (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hdist (q : ℂ) (hq : q ∈ K) : dist q 0 < r := by
    have h := Metric.mem_closedBall.mp hq
    linarith
  have hPK : ContinuousOn P K := hPc.continuousOn.mono fun q hq ↦
    (hball (hdist q hq)).2.2.2.2.1
  have hζK : ContinuousOn ζ K := hζc.continuousOn.mono fun q hq ↦
    (hball (hdist q hq)).2.2.2.2.2
  let S := frontLinearizedC0Semigroup f D c φ h₁ h₂ 0
  let B : ℂ → BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) := fun q ↦ -q • frontComplexifiedDiffusionBUC D
  have hB : ContinuousOn B K := by
    dsimp [B]
    fun_prop
  have hb := S.exists_uniform_complement_bound_on hK hB hPK hζK
    (fun q hq ↦ (hball (hdist q hq)).2.1)
    (fun q hq ↦ (hball (hdist q hq)).2.2.1)
    (fun q hq x ↦ (frontPencilC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ q _ _).mpr
      ((hball (hdist q hq)).2.2.2.1 x))
    (fun q hq ↦ (hball (hdist q hq)).1)
    (ε := θ / 8) (by positivity)
  obtain ⟨M, hM, hb⟩ := hb
  refine ⟨r / 2, by positivity, M, hM, θ, hθ, ?_⟩
  intro q hq t
  have hqK : q ∈ K := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hq
  have hrate : -(θ / 4) + θ / 8 = -(θ / 8) := by ring
  simpa only [hrate, S, B, P, frontPencilC0Semigroup] using! hb q hqK t

/-- The first bound of Lemma 2.3, uniform over the paper's small complex contour box.
The estimate also holds for `0 ≤ t < 1`. -/
theorem exists_frontComplexFrequency_uniform_complement_bound :
    ∃ k > 0, ∃ M > 0, ∃ μ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal),
      ‖ξ₀‖ ≤ k → ‖ξ₁‖ ≤ k →
        ‖(frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t).comp
            (ContinuousLinearMap.id ℂ (BUC ℝ (ℂ^n)) -
              frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃
                (complexFrequencyShift ξ₀ ξ₁))‖ ≤ M * Real.exp (-μ * t) := by
  obtain ⟨r, hr, M, hM, θ, hθ, hb⟩ := exists_frontPencil_uniform_complement_bound f D c φ ψ h₁ h₂ h₃
  let k := Real.sqrt (r / 2)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk2 : k ^ 2 = r / 2 := Real.sq_sqrt (by positivity)
  refine ⟨k, hk, M, hM, θ / 8, by positivity, ?_⟩
  intro ξ₀ ξ₁ t hξ₀ hξ₁
  have hq : ‖complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)‖ ≤ r := by
    apply (norm_complexFrequencyQuadratic_le _).trans
    rw [norm_complexFrequencyShift_sq]
    have h₀ := pow_le_pow_left₀ (norm_nonneg ξ₀) hξ₀ 2
    have h₁ := pow_le_pow_left₀ (norm_nonneg ξ₁) hξ₁ 2
    linarith
  rw [frontComplexFrequencyC0Semigroup_eq_pencil]
  exact hb _ hq t

/-- Lemma 2.3 in full: one frequency box and one set of constants gives complementary
exponential decay and the critical-mode `t⁻¹` Gaussian Taylor remainder. -/
theorem exists_front_lowFrequency_bound :
    ∃ k > 0, ∃ M > 0, ∃ μ > 0, ∃ κ > 0,
      ∀ (ξ₀ ξ₁ : ℝ^m) (t : NNReal), ‖ξ₀‖ ≤ k → ‖ξ₁‖ ≤ k → 1 ≤ t →
        ‖(frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t).comp
            (ContinuousLinearMap.id ℂ (BUC ℝ (ℂ^n)) -
              frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃
                (complexFrequencyShift ξ₀ ξ₁))‖ ≤ M * Real.exp (-μ * t) ∧
        ‖(frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t).comp
              (frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃
                (complexFrequencyShift ξ₀ ξ₁)) -
            Complex.exp (-(t * d_perp D φ ψ : ℂ) *
                complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)) •
              profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)‖ ≤
          (M / t) * Real.exp (-μ * ‖ξ₀‖ ^ 2 * t + κ * ‖ξ₁‖ ^ 2 * t) := by
  obtain ⟨k₁, hk₁, M₁, hM₁, μ₁, hμ₁, hcomp⟩ :=
    exists_frontComplexFrequency_uniform_complement_bound (m := m) f D c φ ψ h₁ h₂ h₃
  obtain ⟨k₂, hk₂, M₂, hM₂, μ₂, hμ₂, κ, hκ, htaylor⟩ :=
    exists_frontCriticalSemigroup_taylor_bound (m := m) f D c φ ψ h₁ h₂ h₃
  refine ⟨min k₁ k₂, lt_min hk₁ hk₂, max M₁ M₂, hM₁.trans_le (le_max_left _ _),
    min μ₁ μ₂, lt_min hμ₁ hμ₂, κ, hκ, ?_⟩
  intro ξ₀ ξ₁ t hξ₀ hξ₁ ht
  constructor
  · apply (hcomp ξ₀ ξ₁ t (hξ₀.trans (min_le_left _ _)) (hξ₁.trans (min_le_left _ _))).trans
    apply mul_le_mul (le_max_left _ _) _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) t.2
  · apply (htaylor ξ₀ ξ₁ t (hξ₀.trans (min_le_right _ _)) (hξ₁.trans (min_le_right _ _)) ht).trans
    apply mul_le_mul (div_le_div_of_nonneg_right (le_max_right _ _) t.2) _
      (Real.exp_pos _).le (div_nonneg (hM₁.le.trans (le_max_left _ _)) t.2)
    apply Real.exp_le_exp.mpr
    apply add_le_add _ le_rfl
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg _)) t.2

end

end Planarwave
