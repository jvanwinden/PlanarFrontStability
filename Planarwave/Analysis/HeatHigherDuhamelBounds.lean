/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialBounds
public import Planarwave.Analysis.HeatHigherRegularity

@[expose] public section

/-!
# The heat Duhamel estimate in every spatial derivative norm

Differentiation commutes with heat averaging and the time integral for the
genuine regular trajectories constructed earlier. Hence the same integral
majorant bounds every spatial derivative, with no derivative loss.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Heat contractivity bounds the Duhamel norm by any continuous source majorant. -/
theorem norm_heatDuhamel_le_integral_on (a : ℝ) {T : ℝ}
    (f : ℝ → BUC E F) {A : ℝ → ℝ} (hA : ContinuousOn A (Icc 0 T))
    (hb : ∀ r ∈ Icc 0 T, ‖f r‖ ≤ A r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖heatDuhamel a f t‖ ≤ ∫ r in (0 : ℝ)..t, A r := by
  apply intervalIntegral.norm_integral_le_of_norm_le ht.1
  · filter_upwards [] with r hr
    exact (norm_heatFlowBUC_le _ _ _).trans (hb r ⟨hr.1.le, hr.2.trans ht.2⟩)
  · exact (hA.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

set_option maxHeartbeats 800000 in
/-- The same majorant controls every derivative through order `k`. -/
theorem BUCSpatialRegularOn.heatDuhamel_bound (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {k : ℕ} {f : ℝ → BUC E F} (hf : BUCSpatialRegularOn (Icc 0 T) k f)
    {A : ℝ → ℝ} (hA : ContinuousOn A (Icc 0 T))
    (hb : ∀ r ∈ Icc 0 T, BUCSpatialBound k (f r) (A r))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    BUCSpatialBound k (Planarwave.heatDuhamel a f t) (∫ r in (0 : ℝ)..t, A r) := by
  induction k generalizing F with
  | zero => exact norm_heatDuhamel_le_integral_on a f hA hb ht
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    refine ⟨norm_heatDuhamel_le_integral_on a f hA (fun r hr ↦ (hb r hr).norm_le) ht,
      Planarwave.heatDuhamel a f' t, ih hf' (fun r hr ↦ (hb r hr).derivative (hd r hr)), ?_⟩
    exact fun x ↦ hasFDerivAt_heatDuhamel_on a hT hc hf'.continuous hd ht x

end

end Planarwave
