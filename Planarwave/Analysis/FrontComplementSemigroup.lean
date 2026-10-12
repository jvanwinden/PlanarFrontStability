/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSpectralSemigroup
import all Planarwave.Analysis.FrontSpectralSeparation
import Planarwave.Analysis.SimpleSpectralRestriction
import Planarwave.Analysis.SemigroupComplementDecay

/-!
# Decay on the front's complementary spectral subspace

This is the individual-frequency step of the first estimate of Lemma 2.3. The
critical eigenvalue is removed by restricting the full generator to `ker P(q)`.
Its remaining spectral gap and inherited sectorial resolvent bound give the rate
`-θ/4`. Uniformization over the compact low-frequency box is a separate step.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The critical projection fixes every vector in the critical pencil kernel. -/
theorem eventually_frontCriticalProjection_fixes_kernel :
    ∀ᶠ q : ℂ in 𝓝 0, ∀ v : ComplexBUC2 (ℂ^n),
      frontCriticalShiftedPencil f D c φ ψ h₁ h₂ h₃ q v = 0 →
        frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q (ComplexBUC2.value (ℂ^n) v) =
          ComplexBUC2.value (ℂ^n) v := by
  let F := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let B := diffusionValue (frontComplexifiedDiffusion D)
  filter_upwards [F.eventually_criticalProjection_fixes_kernel B] with q hq
  intro v hv
  rw [frontCriticalShiftedPencil_eq_criticalPencil f D c φ ψ h₁ h₂ h₃] at hv
  exact hq v hv

variable [Nontrivial (ℝ^n)]

/-- For each sufficiently small complex pencil parameter the complementary semigroup
decays at the paper's individual rate `-θ/4`. No decay hypothesis is added. -/
theorem exists_eventually_frontPencil_complement_bound :
    ∃ θ > 0, ∀ᶠ q : ℂ in 𝓝 0, ∃ M > 0, ∀ t : NNReal,
      ‖(frontPencilC0Semigroup f D c φ h₁ h₂ q t).comp
          (ContinuousLinearMap.id ℂ (BUC ℝ (ℂ^n)) -
            frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q)‖ ≤
        M * Real.exp (-(θ / 4) * t) := by
  obtain ⟨θ, hθ, hgap⟩ :=
    exists_eventually_frontPencil_mem_spectrum_iff_branch_on_gap f D c φ ψ h₁ h₂ h₃
  obtain ⟨a, ha, C, _, Ω, _, hsector⟩ :=
    exists_uniform_frontPencil_sectorial_resolvent_bound f D c φ h₁ h₂
      (show (0 : ℝ) ≤ 1 by norm_num)
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [hgap, eventually_frontCriticalProjection_idempotent f D c φ ψ h₁ h₂ h₃,
    eventually_frontPencilSemigroup_preserves_criticalKernel f D c φ ψ h₁ h₂ h₃,
    eventually_frontCriticalProjection_leftEigenmap f D c φ ψ h₁ h₂ h₃,
    eventually_frontCriticalProjection_eigenrange f D c φ ψ h₁ h₂ h₃,
    eventually_frontCriticalProjection_fixes_kernel f D c φ ψ h₁ h₂ h₃,
    eventually_frontCriticalProjection_spectralSplitting f D c φ ψ h₁ h₂ h₃,
    Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 by norm_num)]
    with q hgapq hP hS hleft hlift hker hsplit hq
  let A := frontPencilClosedOperator f D c φ h₁ h₂ q
  let S := frontPencilC0Semigroup f D c φ h₁ h₂ q
  let P := frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q
  have hnorm : ‖q‖ ≤ 1 := (by simpa only [Metric.mem_ball, dist_zero_right] using hq : ‖q‖ < 1).le
  refine A.exists_complement_bound_of_sectorial_spectrum S
    (frontPencilC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ q) P hP hS hleft hlift hker
    (s := -(θ / 2)) ?_ ha (hsector q hnorm) ?_ ?_
  · intro y hy
    have hyK : y ∈ LinearMap.ker P.toLinearMap := hy
    rw [hsplit.2] at hyK
    exact hyK
  · intro z hz hne
    by_contra! hright
    exact hne ((hgapq z hright.le).mp hz)
  · linarith

/-- The same individual complementary bound in the paper's complex Fourier coordinates. -/
theorem exists_eventually_frontComplexFrequency_complement_bound :
    ∃ θ > 0, ∀ᶠ ξ : ℂ^m in 𝓝 0, ∀ ξ₀ ξ₁ : ℝ^m,
      complexFrequencyShift ξ₀ ξ₁ = ξ → ∃ M > 0, ∀ t : NNReal,
        ‖(frontComplexFrequencyC0Semigroup f D c φ h₁ h₂ ξ₀ ξ₁ t).comp
            (ContinuousLinearMap.id ℂ (BUC ℝ (ℂ^n)) -
              frontCriticalProjectionAtComplexFrequency f D c φ ψ h₁ h₂ h₃ ξ)‖ ≤
          M * Real.exp (-(θ / 4) * t) := by
  obtain ⟨θ, hθ, hb⟩ := exists_eventually_frontPencil_complement_bound f D c φ ψ h₁ h₂ h₃
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [(tendsto_complexFrequencyQuadratic_zero (m := m)).eventually hb] with ξ hξ
  intro ξ₀ ξ₁ hshift
  rw [frontComplexFrequencyC0Semigroup_eq_pencil, hshift]
  exact hξ

end

end Planarwave
