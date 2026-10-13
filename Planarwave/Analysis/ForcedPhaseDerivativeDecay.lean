/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfDerivativeDecay
public import Planarwave.Analysis.ForcedPhaseClassical
public import Planarwave.Analysis.ColeHopfInverseSecondDerivative

@[expose] public section

/-!
# Weighted decay for the classical forced phase

Transfer the estimates for the Cole--Hopf variable to the genuine phase
gradient and Laplacian. The quadratic gradient term in the inverse
Hessian has the same full-power decay as the Hessian itself. This proves
the weighted low-order part of `eq:sigmafullest1` in Step 1 of the paper.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

/-- Squaring half-power decay gives full-power decay. Smallness of the
amplitude keeps the estimate linear in that amplitude. -/
theorem sq_le_full_decay_of_half_decay {u K M t : ℝ}
    (hu : 0 ≤ u) (hM : 0 ≤ M) (hM1 : M ≤ 1) (ht : 0 ≤ t)
    (hb : u ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ))) :
    u ^ 2 ≤ K ^ 2 * M * (1 + t) ^ (-(1 : ℝ)) := by
  have hpow : ((1 + t) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 + t) ^ (-(1 : ℝ)) := by
    rw [pow_two, ← Real.rpow_add (by linarith : 0 < 1 + t)]
    norm_num
  calc
    _ ≤ (K * M * (1 + t) ^ (-(1 / 2 : ℝ))) ^ 2 := pow_le_pow_left₀ hu hb 2
    _ = K ^ 2 * (M * M) * (1 + t) ^ (-(1 : ℝ)) := by rw [mul_pow, hpow]; ring
    _ ≤ K ^ 2 * (1 * M) * (1 + t) ^ (-(1 : ℝ)) := by gcongr
    _ = _ := by ring

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance phaseDecayFirstBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance phaseDecayFirstBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance phaseDecayTensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance phaseDecayTensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance phaseDecaySecondBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
local instance phaseDecaySecondBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance

/-- Weighted decay survives the inverse Cole--Hopf transform in its
small domain, including the quadratic term in the second chain rule. -/
theorem exists_coleHopfInv_gradient_laplacian_decay {β T K₁ K₂ M : ℝ}
    {ξ σ : ℝ → BUC E ℝ} (hξ : ContinuousOn ξ (Icc 0 T))
    (q : ℝ → BUC E (E →L[ℝ] ℝ)) (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ))
    (hqc : ContinuousOn q (Icc 0 T)) (hhc : ContinuousOn h (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x)
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hσ : ∀ t ∈ Icc 0 T, ∀ x, σ t x = coleHopfInv β (ξ t x))
    (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hq : ∀ t ∈ Icc 0 T, ‖q t‖ ≤ K₁ * M * (1 + t) ^ (-(1 / 2 : ℝ)))
    (hh : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ K₂ * M * (1 + t) ^ (-(1 : ℝ))) :
    ∃ (s : ℝ → BUC E E) (L : ℝ → BUC E ℝ),
      ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, (∀ x, s t x = ∇ (σ t : E → ℝ) x) ∧
        (∀ x, L t x = Δ (σ t : E → ℝ) x) ∧
        ‖s t‖ ≤ (2 * K₁) * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
        ‖L t‖ ≤ (‖laplacianTraceCLM (E := E) (F := ℝ)‖ * (2 * K₂ + 4 * |β| * K₁ ^ 2)) *
          M * (1 + t) ^ (-(1 : ℝ)) := by
  obtain ⟨s, hsc, hs⟩ := exists_coleHopfInv_buc_gradient hξ q hqc
    (fun t ht x ↦ (hd t ht x).1) hsmall hσ
  obtain ⟨L, hLc, hL⟩ := exists_coleHopfInv_buc_laplacian hξ q h hqc hhc hd hsmall hσ
  refine ⟨s, L, hsc, hLc, ?_⟩
  intro t ht
  refine ⟨(hs t ht).1, (hL t ht).1, ?_, ?_⟩
  · calc
      ‖s t‖ ≤ 2 * ‖q t‖ := (hs t ht).2
      _ ≤ 2 * (K₁ * M * (1 + t) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hq t ht) (by norm_num)
      _ = _ := by ring
  · have hq2 := sq_le_full_decay_of_half_decay (norm_nonneg (q t)) hM hM1 ht.1 (hq t ht)
    calc
      ‖L t‖ ≤ ‖laplacianTraceCLM (E := E) (F := ℝ)‖ *
          (2 * ‖h t‖ + (4 * |β|) * ‖q t‖ ^ 2) := (hL t ht).2
      _ ≤ ‖laplacianTraceCLM (E := E) (F := ℝ)‖ *
          (2 * (K₂ * M * (1 + t) ^ (-(1 : ℝ))) +
            (4 * |β|) * (K₁ ^ 2 * M * (1 + t) ^ (-(1 : ℝ)))) := by gcongr; exact hh t ht
      _ = _ := by ring

variable [MeasurableSpace E] [BorelSpace E]

/-- Construct the actual classical delayed phase with the uniform value
bound and both weighted derivative bounds. All constants are fixed before
the time horizon, data, and supplied nonlinear source. -/
theorem exists_delayed_forced_phase_derivative_decay (a β C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0, ∀ (c T M : ℝ) (p : BUC E ℝ) (N : ℝ → BUC E ℝ),
      a * β = c / 2 → 0 ≤ T → 0 ≤ M → M ≤ M₀ →
      (∀ t ∈ Icc 0 T, max ‖delayedHeatForcing a p N t‖
        (max ‖delayedHeatForcingFDeriv ha p N t‖ ‖delayedHeatForcingFDeriv2 ha p N t‖) ≤
          C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC E ℝ) (s : ℝ → BUC E E) (L : ℝ → BUC E ℝ),
        IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧ ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧
        σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : E → ℝ) ∧
          (∀ x, s t x = ∇ (σ t : E → ℝ) x) ∧ (∀ x, L t x = Δ (σ t : E → ℝ) x) ∧
          ‖σ t‖ ≤ C₀ * M ∧ ‖s t‖ ≤ C₀ * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
          ‖L t‖ ≤ C₀ * M * (1 + t) ^ (-(1 : ℝ)) ∧ coleHopfBUC β (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r ↦ σ r x)
          (a * L t x + (c / 2) * ‖s t x‖ ^ 2 - delayedHeatForcing a p N t x) t := by
  obtain ⟨A, hA, μ, hμ, hex⟩ := exists_delayed_forced_phase_classical (E := E) β C hC
  let K₁ := (16 * max 1 (Real.sqrt (2 * a))⁻¹) * coleHopfC2SourceConstant β C
  let K₂ := (32 * max 1 a⁻¹) * coleHopfC2SourceConstant β C
  let K₃ := ‖laplacianTraceCLM (E := E) (F := ℝ)‖ * (2 * K₂ + 4 * |β| * K₁ ^ 2)
  have hK₁ : 0 ≤ K₁ := mul_nonneg (by positivity) (coleHopfC2SourceConstant_nonneg β hC.le)
  have hK₂ : 0 ≤ K₂ := mul_nonneg (by positivity) (coleHopfC2SourceConstant_nonneg β hC.le)
  have hK₃ : 0 ≤ K₃ := by dsimp only [K₃]; positivity
  let B := 2 * A + 2 * K₁ + K₃ + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hAB : 2 * A ≤ B := by dsimp only [B]; linarith
  have hKB : 2 * K₁ ≤ B := by dsimp only [B]; linarith
  have hLB : K₃ ≤ B := by dsimp only [B]; linarith
  refine ⟨B, hB, min μ 1, lt_min hμ (by norm_num), ?_⟩
  intro c T M p N hcancel hT hM hMM hdecay
  have hM1 : M ≤ 1 := hMM.trans (min_le_right _ _)
  obtain ⟨ξ, σ, hξ, hσc, hσ0, hb, htime, _⟩ := hex a c T M p N ha hcancel hT hM
    (hMM.trans (min_le_left _ _)) (fun t ht ↦ (le_max_left _ _).trans (hdecay t ht))
  obtain ⟨q, h, hqc, hhc, hd, hqh⟩ :=
    hξ.delayed_exists_buc_second_fderivative_decay ha hT hC.le hM hM1 hdecay
  obtain ⟨s, L, hsc, hLc, hsL⟩ := exists_coleHopfInv_gradient_laplacian_decay
    hξ.continuous q h hqc.continuousOn hhc.continuousOn hd
    (fun t ht ↦ (hb t ht).2.2.1) (fun t ht ↦ (hb t ht).2.2.2.2.1)
    hM hM1 (fun t ht ↦ (hqh t ht).2.1) (fun t ht ↦ (hqh t ht).2.2)
  refine ⟨ξ, σ, s, L, hξ, hσc, hsc, hLc, hσ0, ?_, ?_⟩
  · intro t ht
    refine ⟨(hb t ht).1, (hsL t ht).1, (hsL t ht).2.1, ?_, ?_, ?_, (hb t ht).2.2.2.2.2⟩
    · exact ((hb t ht).2.2.2.1).trans (mul_le_mul_of_nonneg_right hAB hM)
    · apply ((hsL t ht).2.2.1).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKB hM)
        (Real.rpow_nonneg (by linarith [ht.1]) _)
    · apply ((hsL t ht).2.2.2).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLB hM)
        (Real.rpow_nonneg (by linarith [ht.1]) _)
  · intro t ht x
    rw [(hsL t ⟨ht.1.le, ht.2.le⟩).1 x, (hsL t ⟨ht.1.le, ht.2.le⟩).2.1 x]
    exact htime t ht x

end

end Planarwave
