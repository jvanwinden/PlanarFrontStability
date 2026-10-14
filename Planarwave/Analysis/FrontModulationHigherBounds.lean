/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontProfileHigherBounds
import all Planarwave.Analysis.FrontForcedPhaseHigherBounds
import Planarwave.Analysis.SpatialTrackingInterpolation

/-!
# Step 4: higher regularity transfer for the actual front

The phase bound is derived from the original source bootstrap, and all
profile bounds from the original front hypotheses. Transfer a supplied
cut off reaction--diffusion bound through the actual modulation map to
obtain higher spatial bounds for the inverse-modulated perturbation.

The parabolic `C^9` estimate for the cut off reaction--diffusion solution
remains an explicit prerequisite; this file does not assert it or a
self-consistent construction of the nonlinear source.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ ψ : ℝ → ℝ^n)
  (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₁ in
/-- Uniform higher bounds for the cut off inverse-modulated perturbation.
Only the corresponding parabolic bound on `χ • u` remains an input. -/
theorem exists_front_modulated_cutoff_cn_bound (k : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (ξ σ : ℝ → BUC (ℝ^m) ℝ),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      (∀ t ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) →
      ∀ t ∈ Icc 0 T, ∀ (u : BUC (ℝ^m × ℝ) (ℝ^n)) (χ : ℝ),
        |χ| ≤ 1 → BUCSpatialBound k (χ • u) B →
        BUCSpatialBound k
          (χ • (modulationShift (c * t) (σ t) u - frontSplitProfileBUC f D c φ h₂)) C := by
  obtain ⟨P, hP, hp⟩ := exists_frontSplitProfile_cn_bound (m := m) f D c φ ψ h₁ h₂ h₃ k
  obtain ⟨K, hK, μ, hμ, hphase⟩ := exists_front_forced_phase_cn_bound (m := m) f D c φ ψ h₃ k
  have hcomp : 0 < bucSpatialCompositionConstant (1 + K) k :=
    lt_of_lt_of_le zero_lt_one (one_le_bucSpatialCompositionConstant (1 + K) k)
  refine ⟨bucSpatialCompositionConstant (1 + K) k * B + P, by positivity,
    min μ 1, lt_min hμ zero_lt_one, ?_⟩
  intro T M v₀ N ξ σ hT hM hMM hv₀ hN hξ hCH t ht u χ hχ hu
  have hM1 : M ≤ 1 := hMM.trans (min_le_right _ _)
  have hσ := (hphase T M v₀ N ξ σ hT hM (hMM.trans (min_le_left _ _)) hv₀ hN hξ hCH t ht).2
  exact hu.modulationShift_sub_cutoff (hσ.mono (show K * M ≤ K by nlinarith)) hp hχ (c * t)

end

end Planarwave
