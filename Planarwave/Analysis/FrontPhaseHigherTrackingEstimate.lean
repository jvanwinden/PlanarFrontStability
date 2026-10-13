/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontForcedPhaseHigherBounds
import all Planarwave.Analysis.FrontTrackingCriticalDecomposition

/-!
# Higher phase bounds and the full tracking response

Assemble the full Step 1 estimate with Steps 2 and 3 of `lem:key`.
The phase has a uniform `C^k` bound (in particular `C^9`), while the
actual front-semigroup response has the logarithmic tracking bound.
The Cole--Hopf identity and all spatial derivative paths are retained
for the subsequent interpolation and comparison arguments.
The nonlinear source is still supplied; closing it remains separate.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n d : ℕ}

local instance phaseHigherTrackingFullGroup : NormedAddCommGroup (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance phaseHigherTrackingFullSpace : NormedSpace ℂ (BUC (ℝ^d) (ℂ^n)) := inferInstance

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- Uniform higher phase estimates and the logarithmic tracking bound,
for the same constructed phase and its actual front-semigroup response. -/
theorem exists_front_phase_higher_and_tracking_estimates (hd : 2 ≤ d) (k : ℕ) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M → ContinuousOn N (Icc 0 T) →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC (ℝ^(d - 1)) ℝ)
        (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ),
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T ∧
        (∀ j : ℕ, BUCSpatialRegularOn (Icc 0 T) j ξ ∧ BUCSpatialRegularOn (Icc 0 T) j σ) ∧
        ContinuousOn s (Icc 0 T) ∧ ContinuousOn l (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (σ t : ℝ^(d - 1) → ℝ) ∧
          BUCSpatialBound k (σ t) (C * M) ∧
          (∀ y, s t y = ∇ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          (∀ y, l t y = Δ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          ‖s t‖ ≤ C * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
          ‖l t‖ ≤ C * M * (1 + t) ^ (-(1 : ℝ)) ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t ∧
          ‖(frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit (embedSplitSpatial hd v₀) t +
            (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel
              (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) t‖ ≤
            (C * M / (1 + t)) * Real.log (2 + t)) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * l t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  obtain ⟨K, hK, μ, hμ, hp⟩ :=
    exists_front_forced_phase_higher_and_weighted_bounds (m := d - 1) f D c φ ψ h₃ k
  obtain ⟨V, hV, hv⟩ := exists_frontTrackingSpatialDuhamel_decay f D c φ ψ h₃ h₁ h₂ hd K
  have hKC : K ≤ K + V := le_add_of_nonneg_right hV.le
  have hVC : V ≤ K + V := le_add_of_nonneg_left hK.le
  refine ⟨K + V, add_pos hK hV, min μ 1, lt_min hμ (by norm_num), ?_⟩
  intro T M v₀ N hT hM hMM hv₀ hNc hN
  obtain ⟨ξ, σ, s, l, hξ, hreg, hsc, hlc, hσ0, hb, htime⟩ :=
    hp T M v₀ N hT hM (hMM.trans (min_le_left _ _)) hv₀ hN
  have hs : ∀ r ∈ Icc 0 T, ‖s r‖ ≤ K * M * (1 + r) ^ (-(1 / 2 : ℝ)) :=
    fun r hr ↦ (hb r hr).2.2.2.2.1
  have hl : ∀ r ∈ Icc 0 T, ‖l r‖ ≤ K * M * (1 + r) ^ (-(1 : ℝ)) :=
    fun r hr ↦ (hb r hr).2.2.2.2.2.1
  refine ⟨ξ, σ, s, l, hξ, hreg, hsc, hlc, hσ0, ?_, htime⟩
  intro t ht
  obtain ⟨hspace, hσ, hsid, hlid, _, _, hCH⟩ := hb t ht
  have hden : 0 ≤ 1 + t := by linarith [ht.1]
  refine ⟨hspace, hσ.mono (mul_le_mul_of_nonneg_right hKC hM), hsid, hlid, ?_, ?_, hCH, ?_⟩
  · exact (hs t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC hM) (Real.rpow_nonneg hden _))
  · exact (hl t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC hM) (Real.rpow_nonneg hden _))
  · exact (hv T M v₀ N s l hM (hMM.trans (min_le_right _ _)) hv₀ hNc hsc hlc hN hs hl t ht).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hVC hM) hden)
        (Real.log_nonneg (by linarith [ht.1])))

end

end Planarwave
