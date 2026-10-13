/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedPhaseClassical
public import Planarwave.Analysis.ColeHopfInverseSecondDerivative

@[expose] public section

/-!
# Classical forced phases with uniform second-order bounds

Combine the C² version of the paper's Grönwall estimate with the small
inverse Cole--Hopf transform. The gradient and Laplacian in the phase
equation are actual BUC fields, continuous in time, with uniform bounds.
The forcing decay is still an input to be closed by the nonlinear iteration.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance phaseC2FirstBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance phaseC2FirstBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance phaseC2TensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance phaseC2TensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance phaseC2SecondBUCNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
local instance phaseC2SecondBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance

/-- The `k = 2` uniform estimate for the constructed classical phase,
including its actual gradient and Laplacian. Constants and the smallness
threshold are chosen before the horizon and the delayed source. -/
theorem exists_delayed_forced_phase_classical_c2 (β C : ℝ) (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0, ∀ (a c T M : ℝ) (p : BUC E ℝ) (N : ℝ → BUC E ℝ),
      ∀ ha : 0 < a, a * β = c / 2 → 0 ≤ T → 0 ≤ M → M ≤ M₀ →
      (∀ t ∈ Icc 0 T, max ‖delayedHeatForcing a p N t‖
        (max ‖delayedHeatForcingFDeriv ha p N t‖ ‖delayedHeatForcingFDeriv2 ha p N t‖) ≤
          C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC E ℝ) (q : ℝ → BUC E (E →L[ℝ] ℝ))
        (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)) (s : ℝ → BUC E E) (L : ℝ → BUC E ℝ),
        IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧ Continuous q ∧ Continuous h ∧
        ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : E → ℝ) ∧
          (∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x) ∧
          (∀ x, s t x = ∇ (σ t : E → ℝ) x) ∧ (∀ x, L t x = Δ (σ t : E → ℝ) x) ∧
          max ‖ξ t‖ (max ‖q t‖ ‖h t‖) ≤ C₀ * M ∧ max ‖σ t‖ ‖s t‖ ≤ (2 * C₀) * M ∧
          ‖L t‖ ≤ (‖laplacianTraceCLM (E := E) (F := ℝ)‖ *
            (2 * C₀ + 4 * |β| * C₀ ^ 2)) * M ∧ coleHopfBUC β (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r ↦ σ r x)
          (a * L t x + (c / 2) * ‖s t x‖ ^ 2 - delayedHeatForcing a p N t x) t := by
  obtain ⟨A, hA, μ, hμ, hex⟩ := exists_delayed_forced_phase_classical (E := E) β C hC
  let K := 4 * C * Real.exp (16 * |β| * C)
  let B := max A K
  have hB : 0 < B := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨B, hB, min μ 1, lt_min hμ (by norm_num), ?_⟩
  intro a c T M p N ha hcancel hT hM hMM hdecay
  have hMμ : M ≤ μ := hMM.trans (min_le_left _ _)
  have hM1 : M ≤ 1 := hMM.trans (min_le_right _ _)
  obtain ⟨ξ, σ, hξ, hσc, hσ0, hb, htime, _⟩ := hex a c T M p N ha hcancel hT hM hMμ
    (fun t ht ↦ (le_max_left _ _).trans (hdecay t ht))
  obtain ⟨q, h, hqc, hhc, hd, hqh⟩ :=
    hξ.delayed_exists_buc_second_fderivative_bound ha hT hC.le hM hM1 hdecay
  obtain ⟨s, hsc, hs⟩ := exists_coleHopfInv_buc_gradient hξ.continuous q hqc.continuousOn
    (fun t ht x ↦ (hd t ht x).1)
    (fun t ht ↦ (hb t ht).2.2.1) (fun t ht ↦ (hb t ht).2.2.2.2.1)
  obtain ⟨L, hLc, hL⟩ := exists_coleHopfInv_buc_laplacian hξ.continuous q h hqc.continuousOn
    hhc.continuousOn hd (fun t ht ↦ (hb t ht).2.2.1) (fun t ht ↦ (hb t ht).2.2.2.2.1)
  refine ⟨ξ, σ, q, h, s, L, hξ, hσc, hqc, hhc, hsc, hLc, hσ0, ?_, ?_⟩
  · intro t ht
    have hC2 : max ‖ξ t‖ (max ‖q t‖ ‖h t‖) ≤ B * M :=
      (hqh t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
    have hqB : ‖q t‖ ≤ B * M := (le_max_left _ _).trans ((le_max_right _ _).trans hC2)
    have hhB : ‖h t‖ ≤ B * M := (le_max_right _ _).trans ((le_max_right _ _).trans hC2)
    have hq2 : ‖q t‖ ^ 2 ≤ B ^ 2 * M := by
      calc
        _ ≤ (B * M) ^ 2 := pow_le_pow_left₀ (norm_nonneg (q t)) hqB 2
        _ = B ^ 2 * (M * M) := by ring
        _ ≤ B ^ 2 * (1 * M) := by gcongr
        _ = _ := by ring
    refine ⟨(hb t ht).1, hd t ht, (hs t ht).1, (hL t ht).1, hC2, max_le ?_ ?_, ?_,
      (hb t ht).2.2.2.2.2⟩
    · apply ((hb t ht).2.2.2.1).trans
      gcongr
      exact le_max_left _ _
    · calc
        ‖s t‖ ≤ 2 * ‖q t‖ := (hs t ht).2
        _ ≤ 2 * (B * M) := mul_le_mul_of_nonneg_left hqB (by norm_num)
        _ = _ := by ring
    · calc
        ‖L t‖ ≤ ‖laplacianTraceCLM (E := E) (F := ℝ)‖ *
            (2 * ‖h t‖ + (4 * |β|) * ‖q t‖ ^ 2) := (hL t ht).2
        _ ≤ ‖laplacianTraceCLM (E := E) (F := ℝ)‖ *
            (2 * (B * M) + (4 * |β|) * (B ^ 2 * M)) := by gcongr
        _ = _ := by ring
  · intro t ht x
    rw [(hs t ⟨ht.1.le, ht.2.le⟩).1 x, (hL t ⟨ht.1.le, ht.2.le⟩).1 x]
    exact htime t ht x

end

end Planarwave
