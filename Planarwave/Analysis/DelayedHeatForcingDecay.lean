/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingSecondDerivativeBounds
public import Planarwave.Analysis.DelayedPolynomialDecay

@[expose] public section

/-!
# Polynomial decay of the actual delayed forcing

This is the estimate preceding Step 1 of `lem:key`, through order two.
The source decay on each completed block, the cutoff bound, and the
fixed positive heat age yield C² forcing decay without derivatives of
the source. Only source values up to the stated horizon are used.
-/

open Set

namespace Planarwave

noncomputable section

/-- The constant in the C² forcing decay bound, enlarged to be positive. -/
def delayedForcingC2DecayConstant (a γ : ℝ) : ℝ :=
  (‖trackingCutoff‖ * max (max 1 (heatScale a (1 / 8))⁻¹) (a * (1 / 8))⁻¹) * (3 : ℝ) ^ γ + 1

theorem delayedForcingC2DecayConstant_pos (a γ : ℝ) : 0 < delayedForcingC2DecayConstant a γ := by
  unfold delayedForcingC2DecayConstant
  positivity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance forcingDecayTensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance forcingDecayTensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance forcingDecayBUCNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] F)) := inferInstance

/-- A decaying, undifferentiated source gives the same decay for all
forcing derivatives through order two, including the initial pulse. -/
theorem norm_delayedHeatForcing_c2_decay_le {a γ T M : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ)
    (p : BUC E F) (N : ℝ → BUC E F) (hM : 0 ≤ M) (hp : ‖p‖ ≤ M)
    (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    max ‖delayedHeatForcing a p N t‖
      (max ‖delayedHeatForcingFDeriv ha p N t‖ ‖delayedHeatForcingFDeriv2 ha p N t‖) ≤
      delayedForcingC2DecayConstant a γ * M * (1 + t) ^ (-γ) := by
  let H := max (max 1 (heatScale a (1 / 8))⁻¹) (a * (1 / 8))⁻¹
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let R := ‖trackingCutoff‖ * H
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) hH
  have hb : max ‖delayedHeatForcing a p N t‖
      (max ‖delayedHeatForcingFDeriv ha p N t‖ ‖delayedHeatForcingFDeriv2 ha p N t‖) ≤
        (R * (3 : ℝ) ^ γ) * M * (1 + t) ^ (-γ) := by
    apply le_decay_of_delayed_block_bounds hγ hR hM ?_ ?_ ht
    · intro r _ hr
      calc
        _ ≤ trackingCutoff r * (H * ‖p‖) := norm_delayedHeatForcing_c2_initial_le ha p N hr
        _ ≤ ‖trackingCutoff‖ * (H * M) := by
          gcongr
          exact trackingCutoff_le_norm r
        _ = R * M := by ring
    · intro n τ hτ hτT
      have hblock : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1), ‖N r‖ ≤ M * (1 + (n : ℝ)) ^ (-γ) := by
        intro r hr
        have hrT : r ∈ Icc 0 T := ⟨(Nat.cast_nonneg n).trans hr.1, by linarith [hr.2, hτ.1]⟩
        exact (hN r hrT).trans (mul_le_mul_of_nonneg_left
          (one_add_rpow_neg_antitone hγ (Nat.cast_nonneg n) hr.1) hM)
      calc
        _ ≤ trackingCutoff τ * (H * (M * (1 + (n : ℝ)) ^ (-γ))) :=
          norm_delayedHeatForcing_c2_block_le ha p N n hτ hblock
        _ ≤ ‖trackingCutoff‖ * (H * (M * (1 + (n : ℝ)) ^ (-γ))) :=
          mul_le_mul_of_nonneg_right (trackingCutoff_le_norm τ) (by positivity)
        _ = R * (M * (1 + (n : ℝ)) ^ (-γ)) := by ring
  apply hb.trans
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM)
    (Real.rpow_nonneg (by linarith [ht.1]) _)
  change R * (3 : ℝ) ^ γ ≤ R * (3 : ℝ) ^ γ + 1
  linarith

end

end Planarwave
