/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSmoothMultidimensional
public import Planarwave.Analysis.BoundedSmoothDerivatives

@[expose] public section

/-!
# Quantitative heat smoothing at every spatial order

Split off one positive heat interval for each derivative and commute the
remaining derivatives through the heat flow. This iterates the first Gaussian
derivative estimate for Banach-valued data. The fixed-age version is used for
the paper's delayed forcing, whose cutoff keeps its heat age away from zero.
-/

namespace Planarwave

noncomputable section

universe u

variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance heatHigherCLMNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance heatHigherCLMNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance heatHigherCLMCompleteSpace : CompleteSpace (E →L[ℝ] F) := inferInstance
local instance heatHigherBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] F)) := inferInstance

set_option maxHeartbeats 800000 in
/-- Distribute `k` derivatives over `k` heat intervals of length `ε`.
The leftover heat interval is contractive. -/
theorem norm_iteratedFDeriv_heatFlow_le_of_mul_le (k : ℕ) {a ε t : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (ht : (k : ℝ) * ε ≤ t)
    (f : BUC E F) (x : E) :
    ‖iteratedFDeriv ℝ k (heatFlow a t f) x‖ ≤ ‖f‖ / heatScale a ε ^ k := by
  induction k generalizing F t with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero, pow_zero, div_one, heatFlowBUC_apply] using!
      (BUC.norm_apply_le (heatFlowBUC a t f) x).trans (norm_heatFlowBUC_le a t f)
  | succ k ih =>
    have ht' : (k : ℝ) * ε ≤ t - ε := by push_cast at ht; linarith
    have hrest : 0 ≤ t - ε := (mul_nonneg (Nat.cast_nonneg k) hε.le).trans ht'
    let v := heatFlowBUC a ε f
    let g := heatFDerivBUC ha hε f
    have hg : ∀ y, HasFDerivAt v (g y) y := fun y ↦ hasFDerivAt_heatFlow ha hε f y
    have hsplit : heatFlow a t f = heatFlow a (t - ε) v := by
      have hcoe : (v : E → F) = heatFlow a ε f := funext (heatFlowBUC_apply _ _ f)
      rw [hcoe, heatFlow_add_time ha.le hrest hε.le f.uniformContinuous f.norm_apply_le,
        sub_add_cancel]
    rw [← norm_iteratedFDeriv_fderiv, hsplit,
      fderiv_heatFlow_of_hasFDerivAt a (t - ε) v g hg]
    have hih := ih (F := E →L[ℝ] F) ht' g
    calc
      _ ≤ ‖g‖ / heatScale a ε ^ k := by simpa only using! hih
      _ ≤ (‖f‖ / heatScale a ε) / heatScale a ε ^ k :=
        div_le_div_of_nonneg_right (norm_heatFDerivBUC_le ha hε f)
          (pow_nonneg (heatScale_pos_of_pos ha hε).le k)
      _ = ‖f‖ / heatScale a ε ^ (k + 1) := by rw [div_div, pow_succ']

/-- A uniform bound for all derivatives through order `K` after heat age `δ`.
The constant depends only on the diffusion, age, and order, not on the datum. -/
theorem norm_iteratedFDeriv_heatFlow_le_of_age (K k : ℕ) {a δ t : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hk : k ≤ K) (ht : δ ≤ t)
    (f : BUC E F) (x : E) :
    ‖iteratedFDeriv ℝ k (heatFlow a t f) x‖ ≤
      (max 1 (heatScale a (δ / (K + 1)))⁻¹) ^ K * ‖f‖ := by
  have hden : (0 : ℝ) < K + 1 := by positivity
  have hε : 0 < δ / (K + 1) := div_pos hδ hden
  have htime : (k : ℝ) * (δ / (K + 1)) ≤ t := by
    apply le_trans _ ht
    have hk' : (k : ℝ) ≤ K + 1 := by exact_mod_cast (Nat.le_succ_of_le hk)
    calc
      _ ≤ (K + 1) * (δ / (K + 1)) := mul_le_mul_of_nonneg_right hk' hε.le
      _ = δ := by field_simp
  apply (norm_iteratedFDeriv_heatFlow_le_of_mul_le k ha hε htime f x).trans
  rw [div_eq_mul_inv, ← inv_pow, mul_comm ‖f‖]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  exact (pow_le_pow_left₀ (inv_nonneg.mpr (heatScale_pos_of_pos ha hε).le)
    (le_max_right _ _) k).trans
    (pow_le_pow_right₀ (le_max_left _ _) hk)

/-- Positive-time spatial derivatives are genuine bounded uniformly continuous
multilinear-map fields, with the fixed-age bound. -/
theorem exists_buc_iteratedFDeriv_heatFlow (K k : ℕ) {a δ t : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hk : k ≤ K) (ht : δ ≤ t) (f : BUC E F) :
    ∃ g : BUC E (E [×k]→L[ℝ] F),
      (∀ x, g x = iteratedFDeriv ℝ k (heatFlow a t f) x) ∧
      ‖g‖ ≤ (max 1 (heatScale a (δ / (K + 1)))⁻¹) ^ K * ‖f‖ :=
  exists_buc_iteratedFDeriv_of_bounds (contDiff_nat_heatFlow (k + 1) ha (hδ.trans_le ht) f)
    (norm_iteratedFDeriv_heatFlow_le_of_age K k ha hδ hk ht f)
    (norm_iteratedFDeriv_heatFlow_le_of_age (K + 1) (k + 1) ha hδ (Nat.succ_le_succ hk) ht f)

end

end Planarwave
