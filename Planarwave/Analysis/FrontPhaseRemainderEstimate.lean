/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontForcedPhaseDerivativeDecay
import all Planarwave.Analysis.FrontTrackingRemainderDecay
import all Planarwave.Analysis.FrontModulationSource
import all Planarwave.Analysis.FrontDelayedForcing

/-!
# Phase and spatial remainder estimates from source decay

Assemble the weighted low-order part of Step 1 and Step 3a of `lem:key`
for the same constructed classical phase. Only the initial perturbation
and the `5/4` bound on the supplied nonlinear source are inputs. The full
source and the remainder bounds are consequences, not extra hypotheses.
This does not yet construct or close the coupled nonlinear tracking system.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n d : ℕ}

local instance phaseRemainderLongNormedAddCommGroup : NormedAddCommGroup (BUC ℝ (ℂ^n)) := inferInstance
local instance phaseRemainderSliceNormedAddCommGroup : NormedAddCommGroup (BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n))) := inferInstance

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The same classical phase satisfies the weighted derivative bounds,
the full source bound `eq:Ntildeest`, and the remainder bound `eq:west`.
Constants and smallness are chosen uniformly before the data and horizon. -/
theorem exists_front_phase_and_remainder_estimates (hd : 2 ≤ d) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      ∃ (σ : ℝ → BUC (ℝ^(d - 1)) ℝ) (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1)))
        (l : ℝ → BUC (ℝ^(d - 1)) ℝ),
        ContinuousOn σ (Icc 0 T) ∧ ContinuousOn s (Icc 0 T) ∧ ContinuousOn l (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : ℝ^(d - 1) → ℝ) ∧
          (∀ y, s t y = ∇ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          (∀ y, l t y = Δ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          ‖σ t‖ ≤ C * M ∧ ‖s t‖ ≤ C * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
          ‖l t‖ ≤ C * M * (1 + t) ^ (-(1 : ℝ)) ∧
          ‖frontModulationSource f D c φ ψ h₃ (N t) (s t) (l t)
            (frontDelayedForcing f D c φ ψ h₃ v₀ N t)‖ ≤ C * M / (1 + t) ∧
          ‖frontTrackingRemainder f D c φ h₁ h₂ ψ h₃ hd v₀ N s l t‖ ≤
            (C * M / (1 + t)) * Real.log (2 + t)) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * l t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  obtain ⟨K, hK, μ, hμ, hp⟩ :=
    exists_front_forced_phase_derivative_decay_of_source_decay (m := d - 1) f D c φ ψ h₃
  obtain ⟨R, hR, hw⟩ := exists_frontTrackingRemainder_decay f D c φ h₁ h₂ ψ h₃ hd K
  let A := frontModulationSourceDecayConstant f D c φ ψ h₃ K
  have hA : 0 < A := frontModulationSourceDecayConstant_pos f D c φ ψ h₃ K
  let C := K + A + R
  have hKC : K ≤ C := by dsimp only [C]; linarith
  have hAC : A ≤ C := by dsimp only [C]; linarith
  have hRC : R ≤ C := by dsimp only [C]; linarith
  refine ⟨C, by dsimp only [C]; positivity, min μ 1, lt_min hμ (by norm_num), ?_⟩
  intro T M v₀ N hT hM hMM hv₀ hN
  have hM1 : M ≤ 1 := hMM.trans (min_le_right _ _)
  obtain ⟨ξ, σ, s, l, _, hσc, hsc, hlc, hσ0, hb, htime⟩ :=
    hp T M v₀ N hT hM (hMM.trans (min_le_left _ _)) hv₀ hN
  have hs : ∀ r ∈ Icc 0 T, ‖s r‖ ≤ K * M * (1 + r) ^ (-(1 / 2 : ℝ)) :=
    fun r hr ↦ (hb r hr).2.2.2.2.1
  have hl : ∀ r ∈ Icc 0 T, ‖l r‖ ≤ K * M * (1 + r) ^ (-(1 : ℝ)) :=
    fun r hr ↦ (hb r hr).2.2.2.2.2.1
  refine ⟨σ, s, l, hσc, hsc, hlc, hσ0, ?_, htime⟩
  intro t ht
  obtain ⟨hspace, hsid, hlid, hσ, _, _, _⟩ := hb t ht
  have hden : 0 ≤ 1 + t := by linarith [ht.1]
  refine ⟨hspace, hsid, hlid, ?_, ?_, ?_, ?_, ?_⟩
  · exact hσ.trans (mul_le_mul_of_nonneg_right hKC hM)
  · exact (hs t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC hM) (Real.rpow_nonneg hden _))
  · exact (hl t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC hM) (Real.rpow_nonneg hden _))
  · exact (norm_frontModulationSource_decay_le f D c φ ψ h₃ v₀ N (s t) (l t)
      hM hM1 hv₀ hN ht (hs t ht) (hl t ht)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hM) hden)
  · exact (hw T M v₀ N s l hM hM1 hv₀ hN hs hl t ht).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRC hM) hden)
        (Real.log_nonneg (by linarith [ht.1])))

end

end Planarwave
