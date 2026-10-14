/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSectorialResolvent
import all Planarwave.Analysis.ComplexFrequencyCriticalSpectrum

/-!
# Low-frequency spectral separation without a spectral cutoff

Complete the spectral separation in Proposition 2.1(1). The sectorial bound
excludes all sufficiently large spectral parameters in a right half-plane,
uniformly near zero frequency. The already proved compact-window perturbation
argument handles the remaining bounded window. No cutoff remains in the result.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) [Nontrivial (ℝ^n)]

/-- In a fixed right half-plane, the entire spectrum near zero frequency
consists of the critical branch. The quantifier over spectral parameters is
unrestricted, unlike the earlier bounded-window result. -/
theorem exists_eventually_frontPencil_mem_spectrum_iff_branch_on_gap :
    ∃ θ > 0, ∀ᶠ q : ℂ in 𝓝 0, ∀ z : ℂ, -(θ / 2) ≤ z.re →
      (z ∈ (frontPencilClosedOperator f D c φ h₁ h₂ q).spectrum ↔
        z = frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q) := by
  obtain ⟨θ, hθ, hwindow⟩ :=
    exists_eventually_frontLongitudinalPencil_not_bijective_iff_branch_on_bounded_gap
      f D c φ ψ h₁ h₂ h₃
  obtain ⟨a, ha, Ω, hΩ, hsector⟩ :=
    exists_uniform_frontPencil_spectrum_sector_bound f D c φ h₁ h₂ (R := 1) (by norm_num)
  let R := θ / 2 + Ω + (Ω + θ / 2) / a + 1
  have hR : 1 ≤ R := by
    have : 0 ≤ θ / 2 + Ω + (Ω + θ / 2) / a := by positivity
    dsimp [R]
    linarith
  have hbranch : Tendsto (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃) (𝓝 0) (𝓝 0) := by
    simpa only [frontCriticalEigenvalue_zero] using
      (contDiffAt_frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃).continuousAt.tendsto
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    simpa only [Metric.mem_ball, dist_zero_right] using hq
  have hbranchSmall : ∀ᶠ q : ℂ in 𝓝 0,
      ‖frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q‖ < 1 := by
    filter_upwards [hbranch (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using! hq
  refine ⟨θ, hθ, ?_⟩
  filter_upwards [hsmall, hbranchSmall, hwindow R] with q hq hbranchNorm hlocal
  intro z hz
  have hlocal' (hzR : ‖z‖ ≤ R) :
      (z ∈ (frontPencilClosedOperator f D c φ h₁ h₂ q).spectrum ↔
        z = frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q) := hlocal z hzR hz
  constructor
  · intro hspec
    have hw := hsector q hq.le z hspec
    have hre : z.re ≤ Ω := by nlinarith [abs_nonneg z.im]
    have habsre : |z.re| ≤ θ / 2 + Ω := by
      rw [abs_le]
      constructor <;> linarith
    have habsim : |z.im| ≤ (Ω + θ / 2) / a := by
      rw [le_div_iff₀ ha]
      nlinarith
    have hzR : ‖z‖ ≤ R := by
      have hh := (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add habsre habsim)
      dsimp only [R]
      linarith
    exact (hlocal' hzR).mp hspec
  · intro heq
    have hzR : ‖z‖ ≤ R := by rw [heq]; exact hbranchNorm.le.trans hR
    exact (hlocal' hzR).mpr heq

end

end Planarwave
