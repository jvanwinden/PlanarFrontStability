/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontModulationProjection
import all Planarwave.Analysis.FrontTrackingRemainderDecay

/-!
# Identifying the critical term in the actual spatial Duhamel formula

For real modulation data the complex rank-one projection is exactly the
real adjoint amplitude times the translation mode. Commuting this fixed
profile map with heat and the time integral identifies the critical term
with the cancelled residual from Step 3b of `lem:key`.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n d : ℕ}

local instance criticalTrackingLongGroup : NormedAddCommGroup (BUC ℝ (ℂ^n)) := inferInstance
local instance criticalTrackingLongRealSpace : NormedSpace ℝ (BUC ℝ (ℂ^n)) := inferInstance
local instance criticalTrackingLongComplexSpace : NormedSpace ℂ (BUC ℝ (ℂ^n)) := inferInstance
local instance criticalTrackingSliceGroup : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := inferInstance
local instance criticalTrackingSliceRealSpace : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := inferInstance
local instance criticalTrackingSliceComplexSpace : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := inferInstance
local instance criticalTrackingFullGroup : NormedAddCommGroup (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance criticalTrackingFullRealSpace : NormedSpace ℝ (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance criticalTrackingFullComplexSpace : NormedSpace ℂ (BUC (ℝ^d) (ℂ^n)) := inferInstance

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- Reconstruct the neutral component from its real transverse amplitude. -/
def frontCriticalReconstruction : BUC (ℝ^m) ℝ →L[ℝ] BUC (ℝ^m) (BUC ℝ (ℂ^n)) :=
  BUC.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight (translationModeBUC f D c φ ψ h₃))

@[simp]
theorem frontCriticalReconstruction_apply (q : BUC (ℝ^m) ℝ) (y : ℝ^m) (z : ℝ) :
    frontCriticalReconstruction f D c φ ψ h₃ q y z = q y • embed (deriv φ z) := rfl

theorem norm_frontCriticalReconstruction_le (q : BUC (ℝ^m) ℝ) :
    ‖frontCriticalReconstruction f D c φ ψ h₃ q‖ ≤ ‖q‖ * ‖translationModeBUC f D c φ ψ h₃‖ := by
  apply (BUC.norm_le (mul_nonneg (norm_nonneg q) (norm_nonneg _))).mpr
  intro y
  change ‖q y • translationModeBUC f D c φ ψ h₃‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (q.norm_apply_le y) (norm_nonneg _)

/-- The critical heat evolution of real data is the heat evolution of
its real phase amplitude, reconstructed along the original translation mode. -/
theorem frontCriticalHeatEvolution_embedSplitSpatial (hd : 2 ≤ d) (t : NNReal)
    (v : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) :
    frontCriticalHeatEvolution f D c φ ψ h₃ t (spatialSlices hd (embedSplitSpatial hd v)) =
      frontCriticalReconstruction f D c φ ψ h₃
        (heatFlowBUC (d_perp D φ ψ) t (longitudinalPairing ψ h₃.integrable v)) := by
  unfold frontCriticalHeatEvolution frontCriticalReconstruction
  rw [← heatFlowBUC_postcomp]
  congr 1
  apply BUC.ext
  intro y
  apply BUC.ext
  intro z
  simp only [BUC.postcompCLM_apply, profileProjection_apply, BUC.smul_apply,
    phaseFunctional_apply, spatialSlices_embedSplitSpatial, inner_embed,
    integral_complex_ofReal, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    longitudinalPairing_apply]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ)
    (longitudinalPairing ψ h₃.integrable v y) (translationModeBUC f D c φ ψ h₃ z)).symm

variable (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)

include h₁ h₂ in
/-- The complete critical part in the actual Duhamel decomposition is
the cancelled heat residual, including the initial contribution. -/
theorem frontTrackingCriticalDuhamel_eq (hd : 2 ≤ d)
    (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hN : ContinuousOn N (Icc 0 t)) :
    frontCriticalHeatEvolution f D c φ ψ h₃ t.toNNReal (spatialSlices hd (embedSplitSpatial hd v₀)) +
      (∫ r in (0 : ℝ)..t, frontCriticalHeatEvolution f D c φ ψ h₃ (t - r).toNNReal
        (spatialSlices hd (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l r))) =
      frontCriticalReconstruction f D c φ ψ h₃ (frontTrackingCriticalResidual f D c φ ψ h₃ v₀ N t) := by
  let G := fun r ↦ longitudinalPairing ψ h₃.integrable
    (frontModulationSource f D c φ ψ h₃ (N r) (s r) (l r)
      (frontDelayedForcing f D c φ ψ h₃ v₀ N r))
  have hG : ContinuousOn G (Icc 0 t) := by
    simp only [G, longitudinalPairing_frontModulationSource f D c φ ψ h₁ h₂ h₃]
    exact ((longitudinalPairing ψ h₃.integrable).continuous.comp_continuousOn hN).sub
      (continuous_frontDelayedForcing f D c φ ψ h₃ v₀ N).continuousOn
  have hi : IntervalIntegrable (fun r ↦ heatFlowBUC (d_perp D φ ψ) (t - r) (G r)) volume 0 t :=
    ((continuous_heatFlowBUC_joint _).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hG)).intervalIntegrable_of_Icc ht
  have heq : (∫ r in (0 : ℝ)..t, frontCriticalHeatEvolution f D c φ ψ h₃ (t - r).toNNReal
      (spatialSlices hd (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l r))) =
        frontCriticalReconstruction f D c φ ψ h₃ (heatDuhamel (d_perp D φ ψ) G t) := by
    calc
      _ = ∫ r in (0 : ℝ)..t, frontCriticalReconstruction f D c φ ψ h₃
          (heatFlowBUC (d_perp D φ ψ) (t - r) (G r)) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le ht] at hr
        simp only [frontTrackingSpatialSource, frontCriticalHeatEvolution_embedSplitSpatial,
          Real.coe_toNNReal _ (sub_nonneg.mpr hr.2), G]
      _ = _ := (frontCriticalReconstruction f D c φ ψ h₃).intervalIntegral_comp_comm hi
  rw [heq, frontCriticalHeatEvolution_embedSplitSpatial, Real.coe_toNNReal _ ht, ← map_add]
  congr 1
  exact heatDuhamel_frontModulationSource_eq_trackingResidual f D c φ ψ h₁ h₂ h₃ v₀ N s l ht hN

/-- The exact `ζ φ' + w` decomposition for the actual spatial-semigroup
solution driven by the full tracking source. -/
theorem frontTrackingSpatialDuhamel_eq_critical_add_remainder [Nontrivial (ℝ^n)] (hd : 2 ≤ d)
    (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hN : ContinuousOn N (Icc 0 t))
    (hs : ContinuousOn s (Icc 0 t)) (hl : ContinuousOn l (Icc 0 t)) :
    spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit (embedSplitSpatial hd v₀) t +
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel
        (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) t) =
      frontCriticalReconstruction f D c φ ψ h₃ (frontTrackingCriticalResidual f D c φ ψ h₃ v₀ N t) +
      frontTrackingRemainder f D c φ h₁ h₂ ψ h₃ hd v₀ N s l t := by
  rw [frontTrackingSpatialDuhamel_decomposition f D c φ h₁ h₂ ψ h₃ hd v₀ N s l ht hN hs hl,
    frontTrackingCriticalDuhamel_eq f D c φ ψ h₃ h₁ h₂ hd v₀ N s l ht hN]

/-- Steps 3a and 3b together: the actual spatial Duhamel solution obeys
`eq:vkeyest`, conditional on the nonlinear source and phase derivative bounds.
All constants are chosen before the paths, amplitude, and time horizon. -/
theorem exists_frontTrackingSpatialDuhamel_decay [Nontrivial (ℝ^n)] (hd : 2 ≤ d) (K : ℝ) :
    ∃ C > 0, ∀ (T M : ℝ) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
      (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
      (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ),
      0 ≤ M → M ≤ 1 → ‖v₀‖ ≤ M → ContinuousOn N (Icc 0 T) →
      ContinuousOn s (Icc 0 T) → ContinuousOn l (Icc 0 T) →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      (∀ r ∈ Icc 0 T, ‖s r‖ ≤ K * M * (1 + r) ^ (-(1 / 2 : ℝ))) →
      (∀ r ∈ Icc 0 T, ‖l r‖ ≤ K * M * (1 + r) ^ (-(1 : ℝ))) →
      ∀ t ∈ Icc 0 T,
        ‖(frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit (embedSplitSpatial hd v₀) t +
          (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel
            (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) t‖ ≤
          (C * M / (1 + t)) * Real.log (2 + t) := by
  obtain ⟨R, hR, hw⟩ := exists_frontTrackingRemainder_decay f D c φ h₁ h₂ ψ h₃ hd K
  let A := (3 * (3 : ℝ) ^ ((5 : ℝ) / 4) * (∫ z, ‖ψ z‖)) * ‖translationModeBUC f D c φ ψ h₃‖
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (by positivity) (integral_nonneg fun z ↦ norm_nonneg (ψ z))) (norm_nonneg _)
  refine ⟨2 * A + R, by positivity, ?_⟩
  intro T M v₀ N s l hM hM1 hv₀ hNc hsc hlc hN hs hl t ht
  have hden : 0 < 1 + t := by linarith [ht.1]
  have hζ := norm_frontTrackingCriticalResidual_decay_le f D c φ ψ h₃
    (by norm_num : (0 : ℝ) ≤ 5 / 4) v₀ N hM hv₀ hNc (by simpa only [neg_div] using hN) ht
  have hcritical : ‖frontCriticalReconstruction f D c φ ψ h₃
      (frontTrackingCriticalResidual f D c φ ψ h₃ v₀ N t)‖ ≤ A * M / (1 + t) := by
    calc
      _ ≤ ‖frontTrackingCriticalResidual f D c φ ψ h₃ v₀ N t‖ *
          ‖translationModeBUC f D c φ ψ h₃‖ := norm_frontCriticalReconstruction_le f D c φ ψ h₃ _
      _ ≤ ((3 * (3 : ℝ) ^ ((5 : ℝ) / 4) * (∫ z, ‖ψ z‖)) * M *
          (1 + t) ^ (-((5 : ℝ) / 4))) * ‖translationModeBUC f D c φ ψ h₃‖ :=
        mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
      _ = A * M * (1 + t) ^ (-(5 : ℝ) / 4) := by dsimp only [A]; rw [neg_div]; ring
      _ ≤ A * M * (1 + t)⁻¹ := mul_le_mul_of_nonneg_left
        (one_add_rpow_neg_five_quarters_le_inv ht.1) (mul_nonneg hA hM)
      _ = _ := by rw [div_eq_mul_inv]
  have hlog : (1 : ℝ) / 2 ≤ Real.log (2 + t) := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono : Real.log 2 ≤ Real.log (2 + t) := Real.log_le_log (by norm_num) (by linarith [ht.1])
    norm_num at htwo
    linarith
  rw [← norm_spatialSlices hd,
    frontTrackingSpatialDuhamel_eq_critical_add_remainder f D c φ ψ h₃ h₁ h₂ hd v₀ N s l ht.1
      (hNc.mono (Icc_subset_Icc le_rfl ht.2)) (hsc.mono (Icc_subset_Icc le_rfl ht.2))
      (hlc.mono (Icc_subset_Icc le_rfl ht.2))]
  calc
    _ ≤ ‖frontCriticalReconstruction f D c φ ψ h₃ (frontTrackingCriticalResidual f D c φ ψ h₃ v₀ N t)‖ +
        ‖frontTrackingRemainder f D c φ h₁ h₂ ψ h₃ hd v₀ N s l t‖ := norm_add_le _ _
    _ ≤ A * M / (1 + t) + (R * M / (1 + t)) * Real.log (2 + t) :=
      add_le_add hcritical (hw T M v₀ N s l hM hM1 hv₀ hN hs hl t ht)
    _ ≤ (2 * A * M / (1 + t)) * Real.log (2 + t) +
        (R * M / (1 + t)) * Real.log (2 + t) := by
      apply add_le_add _ le_rfl
      calc
        _ = (2 * A * M / (1 + t)) * (1 / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

end

end Planarwave
