/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamelSmoothing
public import Planarwave.Analysis.HeatDuhamelGradientContinuity
public import Planarwave.Analysis.HeatHigherRegularity

@[expose] public section

/-!
# A derivative gain at every order for heat Duhamel

Commute the derivatives already present in the source through Duhamel,
then use the integrable heat-gradient singularity to gain one more.
The bound depends on the source's common `C^k` bound and elapsed time,
not on any pre-existing derivative of order `k+1`.
-/

open Set

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The gained spatial derivative is continuous in the BUC norm in time,
including at zero. Thus the smoothing gain preserves the trajectory
regularity needed for iteration. -/
theorem BUCSpatialRegularOn.heatDuhamel_gain {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    {k : ℕ} {f : ℝ → BUC E F} (hf : BUCSpatialRegularOn (Icc 0 T) k f) :
    BUCSpatialRegularOn (Icc 0 T) (k + 1) (Planarwave.heatDuhamel a f) := by
  induction k generalizing F with
  | zero =>
    obtain ⟨C, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
    refine ⟨continuousOn_heatDuhamel a hT hf, heatDuhamelGradient ha f,
      continuousOn_heatDuhamelGradient ha hT hf, ?_⟩
    intro t ht x
    exact hasFDerivAt_heatDuhamel_smoothing ha ht.1
      (hf.mono (Icc_subset_Icc le_rfl ht.2))
      (fun r hr ↦ hb r ⟨hr.1, hr.2.trans ht.2⟩) x
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    refine ⟨continuousOn_heatDuhamel a hT hc, Planarwave.heatDuhamel a f', ih hf', ?_⟩
    exact fun t ht x ↦ hasFDerivAt_heatDuhamel_on a hT hc hf'.continuous hd ht x

/-- A regular `C^k` source produces a genuinely `C^(k+1)` Duhamel response.
The same constant bounds all derivatives through order `k+1`. -/
theorem BUCSpatialRegularOn.heatDuhamel_smoothing {a T C : ℝ} (ha : 0 < a)
    {k : ℕ} {f : ℝ → BUC E F} (hf : BUCSpatialRegularOn (Icc 0 T) k f)
    (hb : ∀ r ∈ Icc 0 T, BUCSpatialBound k (f r) C)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    BUCSpatialBound (k + 1) (Planarwave.heatDuhamel a f t)
      (C * (t + 2 * Real.sqrt t / Real.sqrt (2 * a))) := by
  have hC : 0 ≤ C := (hb 0 ⟨le_rfl, ht.1.trans ht.2⟩).nonneg
  have hn : ‖Planarwave.heatDuhamel a f t‖ ≤ C * (t + 2 * Real.sqrt t / Real.sqrt (2 * a)) := by
    apply (norm_heatDuhamel_le f ht.1 (fun r hr ↦
      (hb r ⟨hr.1, hr.2.trans ht.2⟩).norm_le)).trans
    have : 0 ≤ 2 * Real.sqrt t / Real.sqrt (2 * a) := by positivity
    nlinarith
  induction k generalizing F with
  | zero =>
    refine ⟨hn, heatDuhamelGradient ha f t, ?_, ?_⟩
    · change ‖heatDuhamelGradient ha f t‖ ≤ _
      apply (norm_heatDuhamelGradient_le ha ht.1
        (fun r hr ↦ hb r ⟨hr.1, hr.2.trans ht.2⟩)).trans
      have : 0 ≤ C * t := mul_nonneg hC ht.1
      calc
        _ = C * (2 * Real.sqrt t / Real.sqrt (2 * a)) := by ring
        _ ≤ _ := by nlinarith
    · exact hasFDerivAt_heatDuhamel_smoothing ha ht.1
        (hf.mono (Icc_subset_Icc le_rfl ht.2))
        (fun r hr ↦ hb r ⟨hr.1, hr.2.trans ht.2⟩)
  | succ k ih =>
    obtain ⟨hfc, f', hf', hd⟩ := hf
    have hb' : ∀ r ∈ Icc 0 T, BUCSpatialBound k (f' r) C :=
      fun r hr ↦ (hb r hr).derivative (hd r hr)
    refine ⟨hn, Planarwave.heatDuhamel a f' t, ih hf' hb' ?_, ?_⟩
    · apply (norm_heatDuhamel_le f' ht.1 (fun r hr ↦
        (hb' r ⟨hr.1, hr.2.trans ht.2⟩).norm_le)).trans
      have : 0 ≤ 2 * Real.sqrt t / Real.sqrt (2 * a) := by positivity
      nlinarith
    · exact hasFDerivAt_heatDuhamel_on a (ht.1.trans ht.2) hfc hf'.continuous hd ht

end

end Planarwave
