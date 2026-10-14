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

The full generator identification turns the real-frequency semigroup estimate of Lemma 2.2
into a quantitative resolvent estimate on a right half-plane. This file also identifies the
concrete resolvent pencil and proves analytic dependence of its graph-domain inverse.
Sectorial bounds and the passage from spectral bounds to semigroup decay are proved separately.
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

/-- At a real wavenumber the closed-operator resolvent is exactly the challenge resolvent. -/
theorem frontPencilClosedOperator_resolventMap_eq (k : ℝ) (z : ℂ) :
    (frontPencilClosedOperator f D c φ h₁ h₂ ((k ^ 2 : ℝ) : ℂ)).resolventMap z =
      frontChallengeResolventMap f D c φ h₁ h₂ k z := by
  ext v a
  simp [ClosedOperator.resolventMap, frontPencilClosedOperator]

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

end

end Planarwave
