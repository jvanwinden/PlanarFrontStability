/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionAnalytic
import all Planarwave.Analysis.FrontLinearizedSemigroup
import all Planarwave.Analysis.FrontCompactSemigroupBounds
import all Planarwave.Analysis.FrontSpectralSemigroup
import Planarwave.Analysis.SemigroupAnalyticPerturbation

/-!
# Analytic generation for the full longitudinal pencil

Section 2 uses analytic semigroups first for the principal diffusion, then for the
reaction perturbation and complex frequencies. The sectorial time extension is now
proved for the actual semigroups at every complex pencil parameter. This is an input
to, not a replacement for, the spectral-to-growth theorem needed in Lemmas 2.3--2.4.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- The reaction multiplier preserves the diffusion family's common analytic
sector. Its exponential loss is independent of the nonnegative Fourier parameter. -/
theorem exists_uniform_frontLinearized_holomorphic_sector :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ M > 0, ∃ ω > 0, ∀ q : ℝ, 0 ≤ q →
      ∃ G : ℂ → (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)),
        AnalyticOnNhd ℂ G (complexTimeSector η) ∧
        (∀ t : ℝ, 0 < t → G t = frontLinearizedC0Semigroup f D c φ h₁ h₂ q t.toNNReal) ∧
        (∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
          G (z + w) = (G z).comp (G w)) ∧
        (∀ v, Tendsto (fun z ↦ G z v) (𝓝[complexTimeSector η] 0) (𝓝 v)) ∧
        (∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖)) := by
  obtain ⟨η, hη, hηhalf, M, hM, ω, hω, hext⟩ :=
    exists_uniform_frontDiffusion_holomorphic_sector D h₁.positive h₁.kernel c
  let B := frontReactionMultiplication f D c φ h₁ h₂
  refine ⟨η, hη, hηhalf, M, hM, ω + M * ‖B‖, by positivity, fun q hq ↦ ?_⟩
  obtain ⟨G, hGa, hreal, _, hzero, hb⟩ := hext q hq
  have hbound : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖) := by
    intro z hz
    exact (hb z hz).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hω.le)) hM.le)
  exact (frontDiffusionC0Semigroup D h₁.positive c q).exists_boundedPerturbation_holomorphic_sector
    B hη hM.le hω.le hGa hbound hreal hzero

/-- Every complex pencil parameter generates an analytic semigroup on the same
time sector, with explicit dependence of the exponential bound on that parameter. -/
theorem exists_frontPencil_holomorphic_sector :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ M > 0, ∃ ω > 0, ∀ q : ℂ,
      ∃ G : ℂ → (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)),
        AnalyticOnNhd ℂ G (complexTimeSector η) ∧
        (∀ t : ℝ, 0 < t → G t = frontPencilC0Semigroup f D c φ h₁ h₂ q t.toNNReal) ∧
        (∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
          G (z + w) = (G z).comp (G w)) ∧
        (∀ v, Tendsto (fun z ↦ G z v) (𝓝[complexTimeSector η] 0) (𝓝 v)) ∧
        (∀ z ∈ complexTimeSector η, ‖G z‖ ≤
          M * Real.exp ((ω + M * ‖q‖ * ‖frontComplexifiedDiffusionBUC D‖) * ‖z‖)) := by
  obtain ⟨η, hη, hηhalf, M, hM, ω, hω, hext⟩ :=
    exists_uniform_frontLinearized_holomorphic_sector f D c φ h₁ h₂
  obtain ⟨G, hGa, hreal, _, hzero, hb⟩ := hext 0 le_rfl
  refine ⟨η, hη, hηhalf, M, hM, ω, hω, fun q ↦ ?_⟩
  obtain ⟨H, hHa, hHreal, hHadd, hHzero, hHb⟩ :=
    (frontLinearizedC0Semigroup f D c φ h₁ h₂ 0).exists_boundedPerturbation_holomorphic_sector
      (-q • frontComplexifiedDiffusionBUC D) hη hM.le hω.le hGa hb hreal hzero
  refine ⟨H, hHa, hHreal, hHadd, hHzero, fun z hz ↦ ?_⟩
  simpa only [norm_smul, norm_neg, mul_assoc] using hHb z hz

end

end Planarwave
