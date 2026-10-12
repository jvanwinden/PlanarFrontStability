/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAllFrequencySemigroup
import Planarwave.Analysis.SemigroupCompactBounds

/-!
# Compact-family uniformization for the longitudinal front semigroups

All members of the pencil are bounded perturbations of the zero-frequency semigroup by
`-q D`. Generator uniqueness identifies this construction with the previously constructed
real-frequency and contour-shift semigroups. The appendix lemma therefore applies to compact
frequency sets. Pointwise decay from the spectral bound remains an explicit hypothesis here;
analytic generation and the spectral-to-growth theorem are not supplied by compactness.
`FrontMidFrequencySemigroup` now discharges those individual decay hypotheses.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- A common base semigroup for every complex member of the longitudinal pencil. -/
def frontPencilC0Semigroup (q : ℂ) : C0Semigroup ℂ (BUC ℝ (ℂ^n)) :=
  (frontLinearizedC0Semigroup f D c φ h₁ h₂ 0).boundedPerturbation
    (-q • frontComplexifiedDiffusionBUC D)

/-- The common-base construction has exactly the full longitudinal pencil as generator. -/
theorem frontPencilC0Semigroup_hasGeneratorAt_iff (q : ℂ) (x y : BUC ℝ (ℂ^n)) :
    (frontPencilC0Semigroup f D c φ h₁ h₂ q).HasGeneratorAt x y ↔
      ∃ v : ComplexBUC2 (ℂ^n), ComplexBUC2.value (ℂ^n) v = x ∧
        frontLongitudinalPencil f D c φ h₁ h₂ q v = y := by
  rw [frontPencilC0Semigroup, C0Semigroup.boundedPerturbation_hasGeneratorAt_iff,
    frontLinearizedC0Semigroup_hasGeneratorAt_iff]
  simp only [Complex.ofReal_zero]
  apply exists_congr
  intro v
  have hshift : frontLongitudinalPencil f D c φ h₁ h₂ q v =
      frontLongitudinalPencil f D c φ h₁ h₂ 0 v +
        (-q • frontComplexifiedDiffusionBUC D) (ComplexBUC2.value (ℂ^n) v) := by
    apply BUC.ext
    intro z
    simp [frontLongitudinalPencil_apply, frontComplexifiedDiffusionBUC, sub_eq_add_neg]
    abel
  constructor
  · rintro ⟨hv, hy⟩
    exact ⟨hv, by rw [hshift, hv, hy, sub_add_cancel]⟩
  · rintro ⟨hv, hy⟩
    rw [hshift, hv] at hy
    exact ⟨hv, eq_sub_iff_add_eq.mpr hy⟩

/-- Rebase the real-frequency construction at frequency zero. -/
theorem frontLinearizedC0Semigroup_eq_pencil (q : ℝ) :
    frontLinearizedC0Semigroup f D c φ h₁ h₂ q =
      frontPencilC0Semigroup f D c φ h₁ h₂ (q : ℂ) := by
  apply C0Semigroup.eq_of_generator_iff
  intro x y
  rw [frontLinearizedC0Semigroup_hasGeneratorAt_iff, frontPencilC0Semigroup_hasGeneratorAt_iff]

/-- The contour-shift construction and the common-base pencil construction are identical. -/
theorem frontComplexFrequencyC0Semigroup_eq_pencil (ξ₀ ξ₁ : ℝ^m) :
    frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ =
      frontPencilC0Semigroup f D c φ h₁ h₂
        (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁)) := by
  apply C0Semigroup.eq_of_generator_iff
  intro x y
  rw [frontComplexFrequencyC0Semigroup_hasGeneratorAt_iff,
    frontPencilC0Semigroup_hasGeneratorAt_iff]

/-- Uniformization for a continuous complex pencil parameter on a compact set. -/
theorem exists_uniform_frontPencil_bound_on {P : Type*} [TopologicalSpace P]
    {K : Set P} (hK : IsCompact K) {q : P → ℂ} (hq : ContinuousOn q K) {ω : ℝ}
    (hpoint : ∀ p ∈ K, ∃ M > 0, ∀ t : NNReal,
      ‖frontPencilC0Semigroup f D c φ h₁ h₂ (q p) t‖ ≤ M * Real.exp (ω * t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M > 0, ∀ p ∈ K, ∀ t : NNReal,
      ‖frontPencilC0Semigroup f D c φ h₁ h₂ (q p) t‖ ≤ M * Real.exp ((ω + ε) * t) := by
  exact (frontLinearizedC0Semigroup f D c φ h₁ h₂ 0).exists_uniform_boundedPerturbation_bound_on
    hK (hq.neg.smul continuousOn_const) hpoint hε

/-- The appendix uniformization applied to the actual real transverse-frequency family. -/
theorem exists_uniform_frontLinearized_bound_on {K : Set (ℝ^m)} (hK : IsCompact K) {ω : ℝ}
    (hpoint : ∀ ξ ∈ K, ∃ M > 0, ∀ t : NNReal,
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ‖ ^ 2) t‖ ≤ M * Real.exp (ω * t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M > 0, ∀ ξ ∈ K, ∀ t : NNReal,
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ‖ ^ 2) t‖ ≤
        M * Real.exp ((ω + ε) * t) := by
  simp_rw [frontLinearizedC0Semigroup_eq_pencil] at hpoint ⊢
  apply exists_uniform_frontPencil_bound_on f D c φ h₁ h₂ hK _ hpoint hε
  exact (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).continuousOn

/-- The compact-annulus step of Lemma 2.4. A pointwise rate `-θ` gives the uniform split rate
`-θ/4 - θ/(4 k₁²) ‖ξ‖²` used to combine the intermediate and high frequencies.
The required pointwise estimate is supplied by `FrontMidFrequencySemigroup`. -/
theorem exists_frontLinearized_midFrequency_bound_of_pointwise {k k₁ θ : ℝ}
    (hk₁ : 1 ≤ k₁) (hθ : 0 < θ)
    (hpoint : ∀ ξ : ℝ^m, k ≤ ‖ξ‖ → ‖ξ‖ ≤ k₁ → ∃ M > 0, ∀ t : NNReal,
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ‖ ^ 2) t‖ ≤ M * Real.exp (-θ * t)) :
    ∃ M > 0, ∀ (ξ : ℝ^m) (t : NNReal), k ≤ ‖ξ‖ → ‖ξ‖ ≤ k₁ →
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ‖ ^ 2) t‖ ≤
        M * Real.exp (-(θ / 4) * t - (θ / (4 * k₁ ^ 2)) * ‖ξ‖ ^ 2 * t) := by
  let K : Set (ℝ^m) := {ξ | k ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ k₁}
  have hK : IsCompact K := by
    have heq : K = Metric.closedBall (0 : ℝ^m) k₁ ∩ {ξ | k ≤ ‖ξ‖} := by
      ext ξ
      simp only [K, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      exact and_comm
    rw [heq]
    exact (isCompact_closedBall (0 : ℝ^m) k₁).inter_right
      (isClosed_le continuous_const continuous_norm)
  obtain ⟨M, hM, hMb⟩ := exists_uniform_frontLinearized_bound_on f D c φ h₁ h₂ hK
    (fun ξ hξ ↦ hpoint ξ hξ.1 hξ.2) (half_pos hθ)
  refine ⟨M, hM, ?_⟩
  intro ξ t hξ hξ₁
  have hk₁pos : 0 < k₁ := zero_lt_one.trans_le hk₁
  have hsq : ‖ξ‖ ^ 2 ≤ k₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ₁ 2
  have hcoef : θ / (4 * k₁ ^ 2) * k₁ ^ 2 = θ / 4 := by
    field_simp
  have hrate : -θ + θ / 2 ≤ -(θ / 4) - θ / (4 * k₁ ^ 2) * ‖ξ‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ θ / (4 * k₁ ^ 2) by positivity)
    rw [hcoef] at h
    linarith
  apply (hMb ξ ⟨hξ, hξ₁⟩ t).trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  simpa only [sub_mul] using! mul_le_mul_of_nonneg_right hrate t.2

end

end Planarwave
