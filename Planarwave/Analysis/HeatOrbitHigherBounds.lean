/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatGradientOperator
public import Planarwave.Analysis.BUCSpatialBounds

@[expose] public section

/-!
# Uniform higher bounds for positive-age heat orbits

Split off a fixed positive heat age before each derivative. The resulting
common bounds and BUC time-continuous derivative fields supply the initial
term in a restarted parabolic regularity argument.
-/

open Set

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 800000 in
/-- A regular initial datum has norm-continuous heat-evolved derivatives. -/
theorem BUCSpatialBound.heatOrbit_regular {k : ℕ} {u : BUC E F} {B : ℝ}
    (hu : BUCSpatialBound k u B) (a : ℝ) :
    BUCSpatialRegularOn univ k (fun t ↦ heatFlowBUC a t u) := by
  induction k generalizing F with
  | zero => exact (continuous_heatFlowBUC_time a u).continuousOn
  | succ k ih =>
    obtain ⟨_, q, hq, hd⟩ := hu
    refine ⟨(continuous_heatFlowBUC_time a u).continuousOn,
      fun t ↦ heatFlowBUC a t q, ih hq, ?_⟩
    exact fun t _ x ↦ hasFDerivAt_heatFlow_of_hasFDerivAt a t u q hd x

set_option maxHeartbeats 800000 in
/-- Uniform `C^k` smoothing after a fixed positive age. The constant is
chosen before the datum and actual heat age. -/
theorem exists_bucSpatialBound_heatFlow (k : ℕ) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∃ C > 0, ∀ t : ℝ, δ ≤ t → ∀ u : BUC E F,
      BUCSpatialBound k (heatFlowBUC a t u) (C * ‖u‖) := by
  induction k generalizing F δ with
  | zero =>
    refine ⟨1, zero_lt_one, fun t ht u ↦ ?_⟩
    simpa only [BUCSpatialBound, one_mul] using norm_heatFlowBUC_le a t u
  | succ k ih =>
    have hhalf : 0 < δ / 2 := by positivity
    obtain ⟨C, hC, hb⟩ := ih (F := E →L[ℝ] F) hhalf
    let K := max 1 (C / heatScale a (δ / 2))
    have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨K, hK, fun t ht u ↦ ?_⟩
    let q := heatFDerivBUC ha hhalf u
    have hrest : δ / 2 ≤ t - δ / 2 := by linarith
    have hsplit : heatFlowBUC a t u =
        heatFlowBUC a (t - δ / 2) (heatFlowBUC a (δ / 2) u) := by
      simpa only [sub_add_cancel] using
        heatFlowBUC_add_apply ha.le (hhalf.le.trans hrest) hhalf.le u
    refine ⟨(norm_heatFlowBUC_le a t u).trans
      (le_mul_of_one_le_left (norm_nonneg u) (le_max_left _ _)),
      heatFlowBUC a (t - δ / 2) q, (hb _ hrest q).mono ?_, ?_⟩
    · calc
        C * ‖q‖ ≤ C * (‖u‖ / heatScale a (δ / 2)) :=
          mul_le_mul_of_nonneg_left (norm_heatFDerivBUC_le ha hhalf u) hC.le
        _ = (C / heatScale a (δ / 2)) * ‖u‖ := by ring
        _ ≤ K * ‖u‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg u)
    · intro x
      rw [hsplit]
      exact hasFDerivAt_heatFlow_of_hasFDerivAt a (t - δ / 2) _ q
        (fun y ↦ hasFDerivAt_heatFlow ha hhalf u y) x

/-- Every positive-age heat orbit has genuine BUC derivative fields of all
finite orders, norm-continuous in time on the whole positive-age interval. -/
theorem bucSpatialRegularOn_heatFlow_of_age (k : ℕ) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (u : BUC E F) :
    BUCSpatialRegularOn (Ici δ) k (fun t ↦ heatFlowBUC a t u) := by
  have hhalf : 0 < δ / 2 := by positivity
  obtain ⟨C, _, hb⟩ := exists_bucSpatialBound_heatFlow (E := E) (F := F) k ha hhalf
  have hreg := (hb _ le_rfl u).heatOrbit_regular a |>.comp_time
    (r := fun t ↦ t - δ / 2) (continuous_id.sub continuous_const)
  apply (hreg.mono (subset_univ (Ici δ))).congr
  intro t ht
  have hrest : 0 ≤ t - δ / 2 := by have := ht; change δ ≤ t at this; linarith
  simpa only [sub_add_cancel] using
    (heatFlowBUC_add_apply ha.le hrest hhalf.le u).symm

end

end Planarwave
