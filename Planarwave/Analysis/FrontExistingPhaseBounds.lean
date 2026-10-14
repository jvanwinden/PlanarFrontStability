/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontForcedPhaseHigherBounds

/-!
# A priori bounds for an existing modulation phase

Step 1 of `lem:key` applies to the phase in the coupled tracking system,
not merely to a separately constructed solution. Uniqueness of the forced
Cole--Hopf mild equation identifies any supplied phase with the previously
constructed phase, and therefore identifies its actual gradient and Laplacian.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- Uniform higher and weighted estimates for any phase whose Cole--Hopf
transform solves the actual delayed forcing equation. In particular, these
estimates apply to an already constructed coupled tracking trajectory. -/
theorem exists_front_existing_phase_higher_and_weighted_bounds (k : ℕ) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (ξ σ : ℝ → BUC (ℝ^m) ℝ)
        (s : ℝ → BUC (ℝ^m) (ℝ^m)) (L : ℝ → BUC (ℝ^m) ℝ),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M →
      (∀ t ∈ Icc 0 T, ‖N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      (∀ t ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) →
      (∀ t ∈ Icc 0 T, ∀ y, s t y = ∇ (σ t : ℝ^m → ℝ) y) →
      (∀ t ∈ Icc 0 T, ∀ y, L t y = Δ (σ t : ℝ^m → ℝ) y) →
      ∀ t ∈ Icc 0 T,
        BUCSpatialBound k (σ t) (C * M) ∧ ‖σ t‖ ≤ C * M ∧
        ‖s t‖ ≤ C * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
        ‖L t‖ ≤ C * M / (1 + t) := by
  obtain ⟨C, hC, M₀, hM₀, hex⟩ :=
    exists_front_forced_phase_higher_and_weighted_bounds (m := m) f D c φ ψ h₃ k
  refine ⟨C, hC, M₀, hM₀, ?_⟩
  intro T M v₀ N ξ σ s L hT hM hMM hv₀ hN hξ hCH hs hL
  obtain ⟨ξ', σ', s', L', hξ', _, _, _, _, hb, _⟩ :=
    hex T M v₀ N hT hM hMM hv₀ hN
  have hξeq : EqOn ξ ξ' (Icc 0 T) := hξ.unique hξ'
    (continuous_frontDelayedForcing f D c φ ψ h₃ v₀ N).continuousOn hT
  have hσeq : EqOn σ σ' (Icc 0 T) := by
    intro t ht
    ext y
    apply (strictMono_coleHopf (c / (2 * d_perp D φ ψ))).injective
    have heq : coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) =
        coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ' t) := by
      rw [hCH t ht, (hb t ht).2.2.2.2.2.2, hξeq ht]
    exact congrArg (fun v : BUC (ℝ^m) ℝ ↦ v y) heq
  intro t ht
  obtain ⟨_, hσb, hs', hL', hsb, hLb, _⟩ := hb t ht
  have hseq : s t = s' t := by
    ext y
    rw [hs t ht y, hσeq ht, ← hs' y]
  have hLeq : L t = L' t := by
    ext y
    rw [hL t ht y, hσeq ht, ← hL' y]
  rw [hσeq ht, hseq, hLeq]
  refine ⟨hσb, hσb.norm_le, hsb, ?_⟩
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hLb

end

end Planarwave
