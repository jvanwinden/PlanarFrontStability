/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontCompactSemigroupBounds
import Planarwave.Analysis.SemigroupClosedOperator

/-!
# Laplace resolvent estimates for the longitudinal front pencil

The full generator identification turns the semigroup estimates of Lemma 2.2 into quantitative
resolvent estimates on right half-planes. The real-frequency estimate also localizes the
semantic `TransverseSpectrum` from the challenge. No spectral-stability hypothesis is needed
for these upper bounds. These results do not yet give a sectorial resolvent estimate or the
converse passage from the spectral bound to semigroup decay.
-/

namespace Planarwave

noncomputable section
open scoped ContDiff

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- Real-frequency right-half-plane resolvent bounds with constants independent of frequency. -/
theorem exists_uniform_frontLinearized_resolvent_bound :
    ∃ M > 0, ∃ μ > 0, ∃ C > 0, ∀ q : ℝ, 0 ≤ q → ∀ z : ℂ, C - μ * q < z.re →
      ∃ hres : (frontPencilClosedOperator f D c φ h₁ h₂ (q : ℂ)).IsInResolvent z,
        ‖(frontPencilClosedOperator f D c φ h₁ h₂ (q : ℂ)).inclusion.comp
          ((frontPencilClosedOperator f D c φ h₁ h₂ (q : ℂ)).resolventInverse z hres)‖ ≤
          M / (z.re - (C - μ * q)) := by
  obtain ⟨M, hM, μ, hμ, C, hC, hbound⟩ := exists_uniform_frontLinearized_bound f D c φ h₁ h₂
  refine ⟨M, hM, μ, hμ, C, hC, ?_⟩
  intro q hq z hz
  let A := frontPencilClosedOperator f D c φ h₁ h₂ (q : ℂ)
  let S := frontLinearizedC0Semigroup f D c φ h₁ h₂ q
  have hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y :=
    frontLinearizedC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ q
  have hb : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp ((C - μ * q) * t) := by
    intro t
    simpa only [sub_mul] using! hbound q hq t
  have hres := A.isInResolvent_of_semigroup_bound S hgen hb z hz
  exact ⟨hres, A.norm_inclusion_resolventInverse_le S hgen hM.le hb z hz hres⟩

/-- The shifted complex-frequency semigroups give a uniform right-half-plane bound too. -/
theorem exists_uniform_frontComplexFrequency_resolvent_bound :
    ∃ M > 0, ∃ μ > 0, ∃ κ > 0, ∀ (ξ₀ ξ₁ : ℝ^m) (z : ℂ),
      κ - μ * ‖ξ₀‖ ^ 2 + κ * ‖ξ₁‖ ^ 2 < z.re →
      ∃ hres : (frontPencilClosedOperator f D c φ h₁ h₂
        (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))).IsInResolvent z,
        ‖(frontPencilClosedOperator f D c φ h₁ h₂
            (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))).inclusion.comp
          ((frontPencilClosedOperator f D c φ h₁ h₂
            (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))).resolventInverse z hres)‖ ≤
          M / (z.re - (κ - μ * ‖ξ₀‖ ^ 2 + κ * ‖ξ₁‖ ^ 2)) := by
  obtain ⟨M, hM, μ, hμ, κ, hκ, hbound⟩ :=
    exists_frontComplexFrequency_allFrequency_bound (m := m) f D c φ h₁ h₂
  refine ⟨M, hM, μ, hμ, κ, hκ, ?_⟩
  intro ξ₀ ξ₁ z hz
  let A := frontPencilClosedOperator f D c φ h₁ h₂
    (complexFrequencyQuadratic (complexFrequencyShift ξ₀ ξ₁))
  let S := frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁
  have hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y :=
    frontComplexFrequencyC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ ξ₀ ξ₁
  have hb : ∀ t : NNReal,
      ‖S t‖ ≤ M * Real.exp ((κ - μ * ‖ξ₀‖ ^ 2 + κ * ‖ξ₁‖ ^ 2) * t) := by
    intro t
    simpa only [add_mul, sub_mul] using! hbound ξ₀ ξ₁ t
  have hres := A.isInResolvent_of_semigroup_bound S hgen hb z hz
  exact ⟨hres, A.norm_inclusion_resolventInverse_le S hgen hM.le hb z hz hres⟩

/-- At a real wavenumber the closed-operator resolvent is exactly the challenge resolvent. -/
theorem frontPencilClosedOperator_resolventMap_eq (k : ℝ) (z : ℂ) :
    (frontPencilClosedOperator f D c φ h₁ h₂ ((k ^ 2 : ℝ) : ℂ)).resolventMap z =
      frontChallengeResolventMap f D c φ h₁ h₂ k z := by
  ext v a
  simp [ClosedOperator.resolventMap, frontPencilClosedOperator]

include h₁ h₂ in
/-- A concrete spectral upper bound, in the exact semantic spectrum of `Challenge.lean`.
This is the growth-bound-to-spectral-bound direction, not its analytic converse. -/
theorem exists_uniform_transverseSpectrum_re_bound :
    ∃ μ > 0, ∃ C > 0, ∀ (k : ℝ) (z : ℂ), z ∈ TransverseSpectrum f D c φ k →
      z.re ≤ C - μ * k ^ 2 := by
  obtain ⟨M, hM, μ, hμ, C, hC, hres⟩ :=
    exists_uniform_frontLinearized_resolvent_bound f D c φ h₁ h₂
  refine ⟨μ, hμ, C, hC, ?_⟩
  intro k z hz
  by_contra! hlt
  obtain ⟨hr, _⟩ := hres (k ^ 2) (sq_nonneg k) z hlt
  have hb : Function.Bijective (frontChallengeResolventMap f D c φ h₁ h₂ k z) := by
    rw [← frontPencilClosedOperator_resolventMap_eq f D c φ h₁ h₂ k z]
    exact hr
  exact (mem_transverseSpectrum_iff_frontChallengeResolventMap_not_bijective
    f D c φ h₁ h₂ k z).mp hz hb

/-- The full common-domain resolvent pencil is jointly holomorphic in transverse parameter
and spectral parameter, as required by the complex-frequency contour argument. -/
theorem contDiff_frontPencil_resolventMap :
    ContDiff ℂ ω (fun p : ℂ × ℂ ↦
      (frontPencilClosedOperator f D c φ h₁ h₂ p.1).resolventMap p.2) := by
  unfold ClosedOperator.resolventMap frontPencilClosedOperator frontLongitudinalPencil
    longitudinalOperator
  fun_prop

/-- At every invertible point, the front resolvent is jointly holomorphic as a map into
operators valued in the full `ComplexBUC2` graph domain. -/
theorem contDiffAt_frontPencil_graphResolvent {p : ℂ × ℂ}
    (hp : (frontPencilClosedOperator f D c φ h₁ h₂ p.1).IsInResolvent p.2) :
    ContDiffAt ℂ ω (fun r : ℂ × ℂ ↦
      (frontPencilClosedOperator f D c φ h₁ h₂ r.1).graphResolvent r.2) p := by
  have hi := ((frontPencilClosedOperator f D c φ h₁ h₂ p.1).isInResolvent_iff_isInvertible p.2).mp hp
  exact hi.contDiffAt_map_inverse.comp p
    (contDiff_frontPencil_resolventMap f D c φ h₁ h₂).contDiffAt

/-- Joint holomorphic dependence in the ambient BUC operator norm. -/
theorem contDiffAt_frontPencil_ambientResolvent {p : ℂ × ℂ}
    (hp : (frontPencilClosedOperator f D c φ h₁ h₂ p.1).IsInResolvent p.2) :
    ContDiffAt ℂ ω (fun r : ℂ × ℂ ↦
      (frontPencilClosedOperator f D c φ h₁ h₂ r.1).ambientResolvent r.2) p := by
  exact contDiffAt_const.clm_comp (contDiffAt_frontPencil_graphResolvent f D c φ h₁ h₂ hp)

end

end Planarwave
