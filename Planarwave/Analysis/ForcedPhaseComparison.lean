/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfComparison

@[expose] public section

/-!
# Final comparison of the forced and unforced phases

Invert `eq:Xfullest` on the small Cole--Hopf range, following the final
paragraph of the paper's proof. Both the comparison constant and the
smallness threshold are independent of the datum and time horizon.
-/

open Set

namespace Planarwave

noncomputable section

section Inverse

variable {E : Type*} [UniformSpace E]

/-- The small-range inverse agrees with the original phase. -/
theorem coleHopfInvSmallBUC_coleHopfBUC (β : ℝ) (u : BUC E ℝ)
    (hsmall : |β| * ‖coleHopfBUC β u‖ ≤ 1 / 2) :
    coleHopfInvSmallBUC β (coleHopfBUC β u) hsmall = u := by
  ext x
  exact coleHopfInv_coleHopf β (u x)

/-- Transfer a difference estimate from the transformed variables back
to their phases, with the paper's uniform inverse bound. -/
theorem norm_sub_le_two_mul_norm_coleHopfBUC_sub (β : ℝ) (u v : BUC E ℝ)
    (hu : |β| * ‖coleHopfBUC β u‖ ≤ 1 / 2)
    (hv : |β| * ‖coleHopfBUC β v‖ ≤ 1 / 2) :
    ‖u - v‖ ≤ 2 * ‖coleHopfBUC β u - coleHopfBUC β v‖ := by
  simpa only [coleHopfInvSmallBUC_coleHopfBUC] using
    norm_coleHopfInvSmallBUC_sub_le β (coleHopfBUC β u) (coleHopfBUC β v) hu hv

end Inverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The final forced/unforced phase estimate. Its hypotheses are exactly
the mild equation, the initial-pulse identity, and the two a priori bounds
used in the paper's final comparison. -/
theorem exists_forcedPhase_comparison_bound (β : ℝ) {P K G : ℝ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C > 0, ∃ ε > 0, ∀ {a T M : ℝ} (p : BUC E ℝ) (g ξ σ : ℝ → BUC E ℝ),
      0 ≤ a → M ∈ Icc 0 ε → ‖p‖ ≤ P * M →
      IsForcedColeHopfMild a β g ξ T → ContinuousOn g (Icc 0 T) →
      (∀ r ∈ Icc 0 (min 1 T), g r = trackingCutoff r • heatFlowBUC a r p) →
      (∀ r ∈ Icc 0 T, coleHopfBUC β (σ r) = ξ r) →
      (∀ r ∈ Icc 0 T, ‖ξ r‖ ≤ K * M) →
      (∀ r ∈ Icc 0 T, ‖g r‖ ≤ G *
        (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) →
      ∀ t ∈ Icc 0 T, ‖σ t - coleHopfEvolution a β t (-p)‖ ≤
        C * (M ^ 2 + M / (1 + t)) := by
  obtain ⟨C, hC, hb⟩ := exists_forcedColeHopf_comparison_bound (E := E) β hP hK hG
  let ε := 1 / (4 * (1 + |β| * (P + K)))
  have hden : 0 < 4 * (1 + |β| * (P + K)) := by positivity
  refine ⟨2 * C, by positivity, ε, by dsimp only [ε]; positivity, ?_⟩
  intro a T M p g ξ σ ha hM hp hξ hg hpulse htransform hξbound hgbound t ht
  have hM0 : 0 ≤ M := hM.1
  have hsum := (le_div_iff₀ hden).mp hM.2
  have hPM : 0 ≤ |β| * (P * M) := by positivity
  have hKM : 0 ≤ |β| * (K * M) := by positivity
  have hM1 : M ≤ 1 := by nlinarith [hM.1]
  have hsmallP : |β| * (P * M) ≤ 1 / 4 := by nlinarith [hM.1]
  have hsmallK : |β| * (K * M) ≤ 1 / 2 := by nlinarith [hM.1]
  have hi : ‖coleHopfBUC β (-p)‖ ≤ 2 * (P * M) := by
    have h := norm_coleHopfBUC_le_two_mul β (-p) (by
      simp only [norm_neg]
      exact (mul_le_mul_of_nonneg_left hp (abs_nonneg β)).trans (by linarith))
    exact h.trans (by simpa only [norm_neg] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2))
  have hsmallforced : |β| * ‖coleHopfBUC β (σ t)‖ ≤ 1 / 2 := by
    rw [htransform t ht]
    exact (mul_le_mul_of_nonneg_left (hξbound t ht) (abs_nonneg β)).trans hsmallK
  have hsmallfree : |β| * ‖coleHopfBUC β (coleHopfEvolution a β t (-p))‖ ≤ 1 / 2 := by
    rw [coleHopfBUC_coleHopfEvolution]
    have h := mul_le_mul_of_nonneg_left ((norm_heatFlowBUC_le a t _).trans hi) (abs_nonneg β)
    nlinarith
  have hcompare := hb p g ξ ha hM.1 hM1 hp (by linarith) hξ hg hpulse hξbound hgbound t ht
  calc
    _ ≤ 2 * ‖coleHopfBUC β (σ t) - coleHopfBUC β (coleHopfEvolution a β t (-p))‖ :=
      norm_sub_le_two_mul_norm_coleHopfBUC_sub β _ _ hsmallforced hsmallfree
    _ = 2 * ‖heatFlowBUC a t (coleHopfBUC β (-p)) - ξ t‖ := by
      rw [htransform t ht, coleHopfBUC_coleHopfEvolution, norm_sub_rev]
    _ ≤ 2 * (C * (M ^ 2 + M / (1 + t))) := mul_le_mul_of_nonneg_left hcompare (by norm_num)
    _ = _ := by ring

/-- The phase comparison for the actual causal forcing construction. The
initial-pulse identity and continuity are discharged, not assumed. -/
theorem exists_delayed_forcedPhase_comparison_bound (β : ℝ) {P K G : ℝ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C > 0, ∃ ε > 0, ∀ {a T M : ℝ} (p : BUC E ℝ) (N ξ σ : ℝ → BUC E ℝ),
      0 ≤ a → M ∈ Icc 0 ε → ‖p‖ ≤ P * M →
      IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T →
      (∀ r ∈ Icc 0 T, coleHopfBUC β (σ r) = ξ r) →
      (∀ r ∈ Icc 0 T, ‖ξ r‖ ≤ K * M) →
      (∀ r ∈ Icc 0 T, ‖delayedHeatForcing a p N r‖ ≤ G *
        (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) →
      ∀ t ∈ Icc 0 T, ‖σ t - coleHopfEvolution a β t (-p)‖ ≤
        C * (M ^ 2 + M / (1 + t)) := by
  obtain ⟨C, hC, ε, hε, hb⟩ := exists_forcedPhase_comparison_bound (E := E) β hP hK hG
  refine ⟨C, hC, ε, hε, ?_⟩
  intro a T M p N ξ σ ha hM hp hξ htransform hξbound hgbound
  exact hb p (delayedHeatForcing a p N) ξ σ ha hM hp hξ
    (continuous_delayedHeatForcing a p N).continuousOn
    (fun r hr ↦ delayedHeatForcing_initial a p N (hr.2.trans (min_le_left _ _)))
    htransform hξbound hgbound

end

end Planarwave
