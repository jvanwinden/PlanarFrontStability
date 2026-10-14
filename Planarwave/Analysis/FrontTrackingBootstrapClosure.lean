/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingAPriori
import all Planarwave.Analysis.FrontTrackingInitialBound
import Planarwave.Analysis.TrackingBootstrapContinuity

/-!
# Closing the bootstrap for an actual coupled tracking solution

This is the final continuity argument of Lemma `key`. The a priori estimates
are applied to restrictions of the same coupled physical tracking solution.
The running supremum supplies their source hypothesis on each restricted
interval, and the resulting improved estimate prevents the bootstrap
functional from reaching one. No source decay is assumed in the conclusion.

This module does not construct the coupled tracking solution: that is the
subsequent causal extension argument in the paper. The positive-amplitude
case is kept separate from the zero-amplitude solution, so no division by
zero is used to extract source bounds from the bootstrap functional.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- The actual coupled tracking solution satisfies the bootstrap bound
and the improved phase, perturbation, and source estimates, without an
assumed nonlinear source bound. Constants are uniform in the time horizon
and in the solution. -/
theorem exists_front_tracking_bootstrap_closed :
    ∃ C > 0, ∃ ε > 0, ∀ {T M : ℝ},
      ∀ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T,
      0 < M → M ≤ ε → ‖X.v₀‖ ≤ M →
      ∀ t ∈ Icc 0 T,
        trackingBootstrapFunctional M X.σ X.N t ≤ 1 / 2 ∧
        ‖X.σ t‖ ≤ C * M ∧
        ‖X.perturbation t‖ ≤ C * M / (1 + t) * Real.log (2 + t) ∧
        ‖X.N t‖ ≤ C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
  obtain ⟨C, hC, μ, hμ, hapriori⟩ :=
    exists_front_tracking_apriori f D c φ ψ h₁ h₂ h₃ hd
  obtain ⟨A, hA, hinitial⟩ :=
    exists_frontTrackingSystem_initial_source_bound f D c φ ψ h₁ h₂ h₃ hd
  let B := 1 + A + 2 * C
  have hB : 0 < B := by dsimp [B]; positivity
  have hBC : 1 + C + C ≤ B := by dsimp [B]; linarith
  have hBA : 1 + A ≤ B := by dsimp [B]; linarith
  obtain ⟨δ, hδ, hδ1, hsmall⟩ := tracking_bootstrap_smallness hB
  refine ⟨C, hC, min μ δ, lt_min hμ hδ, ?_⟩
  intro T M X hM hMε hv₀
  have hMμ := hMε.trans (min_le_left _ _)
  have hMδ := hMε.trans (min_le_right _ _)
  have hM1 : M ≤ 1 := hMδ.trans hδ1
  have hhalf : B * M ^ ((3 : ℝ) / 4) ≤ 1 / 2 := hsmall M hM.le hMδ
  have hMpow : M ≤ M ^ ((3 : ℝ) / 4) :=
    Real.self_le_rpow_of_le_one hM.le hM1 (by norm_num)
  have hσ := X.phase_regular.continuous
  have hηcont := continuousOn_trackingBootstrapFunctional (M := M) hσ X.source_continuous
  obtain ⟨hNzero, hσzero⟩ := hinitial T X M hM.le hM1 hv₀
  have hzero : trackingBootstrapFunctional M X.σ X.N 0 ≤ 1 / 2 := by
    apply (trackingBootstrapFunctional_zero_le X.σ X.N hM hσzero hNzero).trans
    apply le_trans ?_ hhalf
    calc
      (1 + A) * M ≤ (1 + A) * M ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hMpow (by positivity)
      _ ≤ B * M ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hBA (by positivity)
  have himprove : ∀ t ∈ Icc 0 T,
      trackingBootstrapFunctional M X.σ X.N t ≤ 1 →
      trackingBootstrapFunctional M X.σ X.N t ≤ 1 / 2 := by
    intro t ht hη
    have hsource : ∀ s ∈ Icc 0 t, ‖X.N s‖ ≤ M * (1 + s) ^ (-(5 : ℝ) / 4) :=
      fun s hs => (trackingBootstrapFunctional_le_one_bounds hσ X.source_continuous
        hM ht hη).2 s hs |>.2
    have hprefix := hapriori (X.mono ht.1 ht.2) hM.le hMμ hv₀ hsource
    have hbetter := trackingBootstrapFunctional_improved hσ X.source_continuous
      hM hM1 hC.le ht (fun s hs => (hprefix s hs).1)
      (fun s hs => (hprefix s hs).2.2)
    exact hbetter.trans ((mul_le_mul_of_nonneg_right hBC (by positivity)).trans hhalf)
  have hclosed := tracking_bootstrap_of_continuousOn hηcont hzero himprove
  have hsource : ∀ s ∈ Icc 0 T, ‖X.N s‖ ≤ M * (1 + s) ^ (-(5 : ℝ) / 4) :=
    fun s hs => (trackingBootstrapFunctional_le_one_bounds hσ X.source_continuous hM
      ⟨X.nonneg, le_rfl⟩ ((hclosed T ⟨X.nonneg, le_rfl⟩).trans (by norm_num))).2 s hs |>.2
  have hall := hapriori X hM.le hMμ hv₀ hsource
  intro t ht
  exact ⟨hclosed t ht, hall t ht⟩

private theorem nonpos_of_small_linear_envelopes {b C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε)
    (hb : ∀ M : ℝ, 0 < M → M ≤ ε → b ≤ C * M) : b ≤ 0 := by
  by_contra h
  have hbpos : 0 < b := lt_of_not_ge h
  have hsmall := hb (min ε (b / (2 * C)))
    (lt_min hε (by positivity)) (min_le_left _ _)
  have hmul := mul_le_mul_of_nonneg_left (min_le_right ε (b / (2 * C))) hC.le
  have heq : C * (b / (2 * C)) = b / 2 := by field_simp
  rw [heq] at hmul
  linarith

/-- A coupled tracking solution with zero initial perturbation is exactly
the unperturbed solution. This follows by applying the uniform estimates
with arbitrarily small positive amplitude bounds, not by dividing by zero
in the definition of the bootstrap functional. -/
theorem FrontTrackingSystem.vanish_of_initial_zero {T : ℝ}
    (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T) (hzero : X.v₀ = 0) :
    ∀ t ∈ Icc 0 T, X.σ t = 0 ∧ X.perturbation t = 0 ∧ X.N t = 0 := by
  obtain ⟨C, hC, ε, hε, hclosed⟩ :=
    exists_front_tracking_bootstrap_closed f D c φ ψ h₁ h₂ h₃ hd
  have hε' : 0 < min ε 1 := lt_min hε zero_lt_one
  intro t ht
  have hbase : 0 < 1 + t := by linarith [ht.1]
  have hlog : 0 < Real.log (2 + t) := Real.log_pos (by linarith [ht.1])
  have hbounds (M : ℝ) (hM : 0 < M) (hMε : M ≤ min ε 1) :
      ‖X.σ t‖ ≤ C * M ∧
      ‖X.perturbation t‖ ≤ (C / (1 + t) * Real.log (2 + t)) * M ∧
      ‖X.N t‖ ≤ (C * (1 + t) ^ (-(5 : ℝ) / 4)) * M := by
    have hm := hclosed X hM (hMε.trans (min_le_left _ _))
      (by simpa only [hzero, norm_zero] using hM.le) t ht
    refine ⟨hm.2.1, ?_, ?_⟩
    · convert hm.2.2.1 using 1
      ring
    · have hpow : M ^ ((7 : ℝ) / 4) ≤ M :=
        Real.rpow_le_self_of_le_one hM.le (hMε.trans (min_le_right _ _)) (by norm_num)
      calc
        ‖X.N t‖ ≤ C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := hm.2.2.2
        _ ≤ C * M * (1 + t) ^ (-(5 : ℝ) / 4) := by gcongr
        _ = _ := by ring
  refine ⟨norm_le_zero_iff.mp ?_, norm_le_zero_iff.mp ?_, norm_le_zero_iff.mp ?_⟩
  · exact nonpos_of_small_linear_envelopes hC hε' fun M hM hMε =>
      (hbounds M hM hMε).1
  · exact nonpos_of_small_linear_envelopes (by positivity) hε' fun M hM hMε =>
      (hbounds M hM hMε).2.1
  · exact nonpos_of_small_linear_envelopes (by positivity) hε' fun M hM hMε =>
      (hbounds M hM hMε).2.2

/-- The closed estimates also hold at zero amplitude. Unlike the bootstrap
functional, this statement contains no inverse amplitude and is suitable
for the subsequent global continuation argument. -/
theorem exists_front_tracking_unconditional_bounds :
    ∃ C > 0, ∃ ε > 0, ∀ {T M : ℝ},
      ∀ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T,
      0 ≤ M → M ≤ ε → ‖X.v₀‖ ≤ M →
      ∀ t ∈ Icc 0 T,
        ‖X.σ t‖ ≤ C * M ∧
        ‖X.perturbation t‖ ≤ C * M / (1 + t) * Real.log (2 + t) ∧
        ‖X.N t‖ ≤ C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
  obtain ⟨C, hC, ε, hε, hclosed⟩ :=
    exists_front_tracking_bootstrap_closed f D c φ ψ h₁ h₂ h₃ hd
  refine ⟨C, hC, ε, hε, ?_⟩
  intro T M X hM hMε hv₀ t ht
  rcases hM.eq_or_lt with hzero | hpos
  · subst M
    have hvzero : X.v₀ = 0 := norm_le_zero_iff.mp hv₀
    obtain ⟨hσ, hv, hN⟩ := X.vanish_of_initial_zero f D c φ ψ h₁ h₂ h₃ hd hvzero t ht
    simp only [hσ, hv, hN, norm_zero, mul_zero, zero_div, zero_mul,
      Real.zero_rpow (by norm_num : (7 : ℝ) / 4 ≠ 0), le_refl, and_self]
  · exact (hclosed X hpos hMε hv₀ t ht).2

end

end Planarwave
