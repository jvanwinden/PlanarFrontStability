/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontPhaseRemainderEstimate
import all Planarwave.Analysis.FrontTrackingCriticalDecomposition

/-!
# The phase and full tracking response from source decay

Combine the constructed classical phase with Steps 3a and 3b of `lem:key`.
The spatial response is the actual front-semigroup Duhamel solution,
not just its remainder. The source `N` is still supplied; constructing
and closing the coupled nonlinear system remains a separate obligation.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n d : ℕ}

local instance phaseTrackingFullGroup : NormedAddCommGroup (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance phaseTrackingFullSpace : NormedSpace ℂ (BUC (ℝ^d) (ℂ^n)) := inferInstance

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The low-order phase estimates and `eq:vkeyest` hold for the same
constructed phase and actual spatial response. No phase-derivative or
full-source estimates are inputs. -/
theorem exists_front_phase_and_tracking_estimates (hd : 2 ≤ d) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M → ContinuousOn N (Icc 0 T) →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      ∃ (σ : ℝ → BUC (ℝ^(d - 1)) ℝ) (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1)))
        (l : ℝ → BUC (ℝ^(d - 1)) ℝ),
        ContinuousOn σ (Icc 0 T) ∧ ContinuousOn s (Icc 0 T) ∧ ContinuousOn l (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : ℝ^(d - 1) → ℝ) ∧
          (∀ y, s t y = ∇ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          (∀ y, l t y = Δ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          ‖σ t‖ ≤ C * M ∧ ‖s t‖ ≤ C * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
          ‖l t‖ ≤ C * M * (1 + t) ^ (-(1 : ℝ)) ∧
          ‖(frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit (embedSplitSpatial hd v₀) t +
            (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel
              (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) t‖ ≤
            (C * M / (1 + t)) * Real.log (2 + t)) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * l t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  obtain ⟨K, hK, μ, hμ, hp⟩ := exists_front_phase_and_remainder_estimates f D c φ h₁ h₂ ψ h₃ hd
  obtain ⟨V, hV, hv⟩ := exists_frontTrackingSpatialDuhamel_decay f D c φ ψ h₃ h₁ h₂ hd K
  have hKC : K ≤ K + V := le_add_of_nonneg_right hV.le
  have hVC : V ≤ K + V := le_add_of_nonneg_left hK.le
  refine ⟨K + V, add_pos hK hV, min μ 1, lt_min hμ (by norm_num), ?_⟩
  intro T M v₀ N hT hM hMM hv₀ hNc hN
  obtain ⟨σ, s, l, hσc, hsc, hlc, hσ0, hb, htime⟩ :=
    hp T M v₀ N hT hM (hMM.trans (min_le_left _ _)) hv₀ hN
  have hs : ∀ r ∈ Icc 0 T, ‖s r‖ ≤ K * M * (1 + r) ^ (-(1 / 2 : ℝ)) :=
    fun r hr ↦ (hb r hr).2.2.2.2.1
  have hl : ∀ r ∈ Icc 0 T, ‖l r‖ ≤ K * M * (1 + r) ^ (-(1 : ℝ)) :=
    fun r hr ↦ (hb r hr).2.2.2.2.2.1
  refine ⟨σ, s, l, hσc, hsc, hlc, hσ0, ?_, htime⟩
  intro t ht
  obtain ⟨hspace, hsid, hlid, hσ, _, _, _, _⟩ := hb t ht
  have hden : 0 ≤ 1 + t := by linarith [ht.1]
  refine ⟨hspace, hsid, hlid, ?_, ?_, ?_, ?_⟩
  · exact hσ.trans (mul_le_mul_of_nonneg_right hKC hM)
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
