/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedPhaseClassical
public import Planarwave.Analysis.ForcedColeHopfFirstDerivativeBounds
public import Planarwave.Analysis.ColeHopfInverseDerivative
public import Planarwave.Analysis.DelayedHeatForcingFirstDerivativeBounds

@[expose] public section

/-!
# Classical forced phases with uniform C¹ bounds

Combine the constructed classical solution, the first-jet Grönwall
estimate, and the genuine inverse gradient. This is the first-order
a priori bound of `lem:xiAP`, with constants chosen before the horizon
and the delayed nonlinear source.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Construct the classical phase, its actual BUC gradient, and a genuine
BUC derivative of the Cole--Hopf variable, with uniform C¹ estimates. -/
theorem exists_delayed_forced_phase_classical_c1 (β C : ℝ) (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0, ∀ (a c T M : ℝ) (p : BUC E ℝ) (N : ℝ → BUC E ℝ),
      ∀ ha : 0 < a, a * β = c / 2 → 0 ≤ T → 0 ≤ M → M ≤ M₀ →
      (∀ t ∈ Icc 0 T, max ‖delayedHeatForcing a p N t‖ ‖delayedHeatForcingFDeriv ha p N t‖ ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC E ℝ) (q : ℝ → BUC E (E →L[ℝ] ℝ)) (s : ℝ → BUC E E),
        IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧ Continuous q ∧ ContinuousOn s (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : E → ℝ) ∧
          (∀ x, HasFDerivAt (ξ t) (q t x) x) ∧ (∀ x, s t x = ∇ (σ t : E → ℝ) x) ∧
          max ‖ξ t‖ ‖q t‖ ≤ C₀ * M ∧ max ‖σ t‖ ‖s t‖ ≤ (2 * C₀) * M ∧
          coleHopfBUC β (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r ↦ σ r x)
          (a * Δ (σ t : E → ℝ) x + (c / 2) * ‖s t x‖ ^ 2 -
            delayedHeatForcing a p N t x) t := by
  obtain ⟨A, hA, μ, hμ, hex⟩ := exists_delayed_forced_phase_classical (E := E) β C hC
  let K := 4 * C * Real.exp (8 * |β| * C)
  refine ⟨max A K, lt_of_lt_of_le hA (le_max_left _ _), min μ 1,
    lt_min hμ (by norm_num), ?_⟩
  intro a c T M p N ha hcancel hT hM hMM hdecay
  have hMμ : M ≤ μ := hMM.trans (min_le_left _ _)
  have hM1 : M ≤ 1 := hMM.trans (min_le_right _ _)
  obtain ⟨ξ, σ, hξ, hσc, hσ0, hb, htime, _⟩ := hex a c T M p N ha hcancel hT hM hMμ
    (fun t ht ↦ (le_max_left _ _).trans (hdecay t ht))
  obtain ⟨q, hqc, hqd, hqb⟩ :=
    hξ.delayed_exists_buc_fderivative_bound ha hT hC.le hM hM1 hdecay
  obtain ⟨s, hsc, hs⟩ := exists_coleHopfInv_buc_gradient hξ.continuous q hqc.continuousOn hqd
    (fun t ht ↦ (hb t ht).2.2.1) (fun t ht ↦ (hb t ht).2.2.2.2.1)
  refine ⟨ξ, σ, q, s, hξ, hσc, hqc, hsc, hσ0, ?_, ?_⟩
  · intro t ht
    have hC1 : max ‖ξ t‖ ‖q t‖ ≤ max A K * M :=
      (hqb t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
    refine ⟨(hb t ht).1, hqd t ht, (hs t ht).1, hC1, max_le ?_ ?_, (hb t ht).2.2.2.2.2⟩
    · apply ((hb t ht).2.2.2.1).trans
      gcongr
      exact le_max_left _ _
    · calc
        ‖s t‖ ≤ 2 * ‖q t‖ := (hs t ht).2
        _ ≤ 2 * (max A K * M) := mul_le_mul_of_nonneg_left
          ((le_max_right _ _).trans hC1) (by norm_num)
        _ = _ := by ring
  · intro t ht x
    rw [(hs t ⟨ht.1.le, ht.2.le⟩).1 x]
    exact htime t ht x

end

end Planarwave
