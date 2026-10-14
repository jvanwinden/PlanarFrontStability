/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingFirstDerivativeBounds
public import Planarwave.Analysis.DelayedHeatForcingSecondDerivative

@[expose] public section

/-!
# Second derivative bounds for the delayed forcing blocks

Identify the actual Hessian on each pulse by uniqueness of derivatives.
The fixed positive heat age then bounds the entire C² forcing norm by
the undifferentiated initial datum or completed source block.
-/

open Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance forcingC2TensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance forcingC2TensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance forcingC2BUCNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] F)) := inferInstance

theorem delayedHeatForcingFDeriv2_initial {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) {t : ℝ} (ht : t ≤ 1) :
    delayedHeatForcingFDeriv2 ha p N t = trackingHeatPulseFDeriv2 ha p t := by
  ext x : 1
  have hd := hasFDerivAt_delayedHeatForcingFDeriv ha p N t x
  rw [delayedHeatForcingFDeriv_initial ha p N ht] at hd
  exact hd.unique (hasFDerivAt_trackingHeatPulseFDeriv ha p t x)

theorem delayedHeatForcingFDeriv2_block {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (k : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    delayedHeatForcingFDeriv2 ha p N ((k : ℝ) + 1 + τ) =
      trackingHeatPulseFDeriv2 ha (delayedHeatBlock a N k) τ := by
  ext x : 1
  have hd := hasFDerivAt_delayedHeatForcingFDeriv ha p N ((k : ℝ) + 1 + τ) x
  rw [delayedHeatForcingFDeriv_block ha p N k hτ] at hd
  exact hd.unique (hasFDerivAt_trackingHeatPulseFDeriv ha (delayedHeatBlock a N k) τ x)

/-- The initial forcing pulse has a C² bound from the datum alone. -/
theorem norm_delayedHeatForcing_c2_initial_le {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) {t : ℝ} (ht : t ≤ 1) :
    max ‖delayedHeatForcing a p N t‖
      (max ‖delayedHeatForcingFDeriv ha p N t‖ ‖delayedHeatForcingFDeriv2 ha p N t‖) ≤
      trackingCutoff t * (max (max 1 (heatScale a (1 / 8))⁻¹) (a * (1 / 8))⁻¹ * ‖p‖) := by
  have hC1 := (norm_delayedHeatForcing_c1_initial_le ha p N ht).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_max_left _ ((a * (1 / 8))⁻¹))
        (norm_nonneg p)) (trackingCutoff_nonneg t))
  refine max_le ((le_max_left _ _).trans hC1) (max_le ((le_max_right _ _).trans hC1) ?_)
  rw [delayedHeatForcingFDeriv2_initial ha p N ht]
  apply (norm_trackingHeatPulseFDeriv2_le ha p t).trans
  apply mul_le_mul_of_nonneg_left _ (trackingCutoff_nonneg t)
  rw [div_eq_mul_inv, mul_comm ‖p‖]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg p)

/-- On a later block, all derivatives through order two are controlled
by a supremum bound on the completed source, with no source derivatives. -/
theorem norm_delayedHeatForcing_c2_block_le {a : ℝ} (ha : 0 < a)
    (p : BUC E F) (N : ℝ → BUC E F) (k : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ∀ r ∈ Icc (k : ℝ) ((k : ℝ) + 1), ‖N r‖ ≤ M) :
    max ‖delayedHeatForcing a p N ((k : ℝ) + 1 + τ)‖
      (max ‖delayedHeatForcingFDeriv ha p N ((k : ℝ) + 1 + τ)‖
        ‖delayedHeatForcingFDeriv2 ha p N ((k : ℝ) + 1 + τ)‖) ≤
      trackingCutoff τ * (max (max 1 (heatScale a (1 / 8))⁻¹) (a * (1 / 8))⁻¹ * M) := by
  have hK : 0 ≤ max (max 1 (heatScale a (1 / 8))⁻¹) (a * (1 / 8))⁻¹ :=
    le_trans (le_trans (by norm_num) (le_max_left _ _)) (le_max_left _ _)
  have hb := norm_delayedHeatForcing_c2_initial_le ha (delayedHeatBlock a N k) N hτ.2
  rw [delayedHeatForcing_initial a (delayedHeatBlock a N k) N hτ.2,
    delayedHeatForcingFDeriv_initial ha (delayedHeatBlock a N k) N hτ.2,
    delayedHeatForcingFDeriv2_initial ha (delayedHeatBlock a N k) N hτ.2] at hb
  rw [delayedHeatForcing_block a p N k hτ, delayedHeatForcingFDeriv_block ha p N k hτ,
    delayedHeatForcingFDeriv2_block ha p N k hτ]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (norm_delayedHeatBlock_le a N k hN) hK) (trackingCutoff_nonneg τ))

end

end Planarwave
