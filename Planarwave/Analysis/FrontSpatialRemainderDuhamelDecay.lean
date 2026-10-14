/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSpatialDecay
import all Planarwave.Analysis.FrontFourierDecomposition
import Planarwave.Analysis.LogarithmicConvolution
import Planarwave.Analysis.HeatDuhamel

/-!
# Logarithmic decay of the spatial Duhamel remainder

Apply the borderline convolution estimate to the actual spatial
semigroup minus its critical heat term. This is the analytic estimate
in Step 3a of `lem:key`, with a supplied `1/(1+t)` source bound.
The tracking argument must still establish that bound for its source.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n d : ℕ}

local instance remainderDuhamelLongNormedAddCommGroup : NormedAddCommGroup (BUC ℝ (ℂ^n)) := inferInstance
local instance remainderDuhamelLongNormedSpace : NormedSpace ℝ (BUC ℝ (ℂ^n)) := inferInstance
local instance remainderDuhamelLongComplexNormedSpace : NormedSpace ℂ (BUC ℝ (ℂ^n)) := inferInstance
local instance remainderDuhamelNormedAddCommGroup :
    NormedAddCommGroup (BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n))) := inferInstance
local instance remainderDuhamelNormedSpace : NormedSpace ℝ (BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n))) := inferInstance
local instance remainderDuhamelComplexNormedSpace : NormedSpace ℂ (BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n))) := inferInstance
local instance remainderDuhamelInputNormedAddCommGroup : NormedAddCommGroup (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance remainderDuhamelInputNormedSpace : NormedSpace ℂ (BUC (ℝ^d) (ℂ^n)) := inferInstance

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The remainder of the actual spatial evolution after its critical
heat component has been subtracted, in isometric slice coordinates. -/
def frontSpatialRemainder (hd : 2 ≤ d) (t : NNReal) (v : BUC (ℝ^d) (ℂ^n)) :
    BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n)) :=
  spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) -
    frontCriticalHeatEvolution f D c φ ψ h₃ t (spatialSlices hd v)

/-- Initial and forced contributions to the remainder in `eq:winfbaseest`. -/
def frontSpatialRemainderDuhamel (hd : 2 ≤ d) (v₀ : BUC (ℝ^d) (ℂ^n))
    (G : ℝ → BUC (ℝ^d) (ℂ^n)) (t : ℝ) : BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n)) :=
  frontSpatialRemainder f D c φ h₁ h₂ ψ h₃ hd t.toNNReal v₀ +
    ∫ r in (0 : ℝ)..t, frontSpatialRemainder f D c φ h₁ h₂ ψ h₃ hd (t - r).toNNReal (G r)

/-- The actual semigroup's remainder has the paper's logarithmic decay
when the forcing has the `1/(1+t)` bound from Step 3a. The constant is
chosen before the horizon, source, and initial perturbation. -/
theorem exists_frontSpatialRemainderDuhamel_decay (hd : 2 ≤ d) :
    ∃ C > 0, ∀ (T M : ℝ) (v₀ : BUC (ℝ^d) (ℂ^n)) (G : ℝ → BUC (ℝ^d) (ℂ^n)),
      0 ≤ M → ‖v₀‖ ≤ M → (∀ r ∈ Icc 0 T, ‖G r‖ ≤ M / (1 + r)) →
      ∀ t ∈ Icc 0 T, ‖frontSpatialRemainderDuhamel f D c φ h₁ h₂ ψ h₃ hd v₀ G t‖ ≤
        (C * M / (1 + t)) * Real.log (2 + t) := by
  obtain ⟨C, hC, hb⟩ := exists_frontSpatialC0Semigroup_remainder_bound f D c φ h₁ h₂ ψ h₃ hd
  refine ⟨4 * C, by positivity, ?_⟩
  intro T M v₀ G hM hv₀ hG t ht
  have hinit : ‖frontSpatialRemainder f D c φ h₁ h₂ ψ h₃ hd t.toNNReal v₀‖ ≤
      (C * M) / (1 + t) := by
    have h := hb t.toNNReal v₀
    rw [Real.coe_toNNReal _ ht.1] at h
    exact h.trans (by
      calc
        _ ≤ (C / (1 + t)) * M := mul_le_mul_of_nonneg_left hv₀
          (div_nonneg hC.le (by linarith [ht.1]))
        _ = _ := by ring)
  have hsource : ∀ r ∈ Icc 0 t,
      ‖frontSpatialRemainder f D c φ h₁ h₂ ψ h₃ hd (t - r).toNNReal (G r)‖ ≤
        (C * M) * ((1 + t - r)⁻¹ * (1 + r)⁻¹) := by
    intro r hr
    have h := hb (t - r).toNNReal (G r)
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hr.2)] at h
    apply h.trans
    calc
      _ ≤ (C / (1 + (t - r))) * (M / (1 + r)) :=
        mul_le_mul_of_nonneg_left (hG r ⟨hr.1, hr.2.trans ht.2⟩)
          (div_nonneg hC.le (by linarith [hr.2]))
      _ = _ := by ring
  have h := norm_add_integral_le_logarithmic_convolution ht.1 (mul_nonneg hC.le hM)
    _ _ hinit hsource
  simpa only [frontSpatialRemainderDuhamel, mul_assoc] using h

/-- The remainder really is the difference between the spatial Duhamel
trajectory and its critical heat trajectory. Both integrals are justified
by strong continuity on the time interval. -/
theorem frontSpatialDuhamel_decomposition (hd : 2 ≤ d) (v₀ : BUC (ℝ^d) (ℂ^n))
    (G : ℝ → BUC (ℝ^d) (ℂ^n)) {t : ℝ} (ht : 0 ≤ t) (hG : ContinuousOn G (Icc 0 t)) :
    spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v₀ t +
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel G t) =
      (frontCriticalHeatEvolution f D c φ ψ h₃ t.toNNReal (spatialSlices hd v₀) +
        ∫ r in (0 : ℝ)..t, frontCriticalHeatEvolution f D c φ ψ h₃ (t - r).toNNReal (spatialSlices hd (G r))) +
      frontSpatialRemainderDuhamel f D c φ h₁ h₂ ψ h₃ hd v₀ G t := by
  let S : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) := frontSpatialC0Semigroup f D c φ h₁ h₂ hd
  let A : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n)) := spatialSlicesCLM ℂ hd
  have hSc : ContinuousOn (fun r ↦ S (t - r).toNNReal (G r)) (Icc 0 t) := by
    have htime : ContinuousOn (fun r : ℝ ↦ t - r) (Icc 0 t) := continuousOn_const.sub continuousOn_id
    simpa only [C0Semigroup.realOrbit, Function.comp_def] using!
      S.continuous_realOrbit_joint.comp_continuousOn (htime.prodMk hG)
  have hAc : ContinuousOn (fun r ↦ A (S (t - r).toNNReal (G r))) (Icc 0 t) :=
    A.continuous.comp_continuousOn hSc
  let P : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n)) :=
    (BUC.postcompCLM (profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃))).comp A
  have hage : Continuous (fun r : ℝ ↦ ((t - r).toNNReal : ℝ)) :=
    continuous_subtype_val.comp (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  have hPc : ContinuousOn (fun r ↦ frontCriticalHeatEvolution f D c φ ψ h₃
      (t - r).toNNReal (spatialSlices hd (G r))) (Icc 0 t) := by
    change ContinuousOn (fun r ↦ heatFlowBUC (d_perp D φ ψ)
      ((t - r).toNNReal : ℝ) (P (G r))) (Icc 0 t)
    simpa only [Function.comp_def] using!
      (continuous_heatFlowBUC_joint (E := ℝ^(d - 1)) (F := BUC ℝ (ℂ^n))
        (d_perp D φ ψ)).comp_continuousOn
          (hage.continuousOn.prodMk (P.continuous.comp_continuousOn hG))
  have hcomm := A.intervalIntegral_comp_comm (hSc.intervalIntegrable_of_Icc (μ := volume) ht)
  change A (S t.toNNReal v₀ + ∫ r in (0 : ℝ)..t, S (t - r).toNNReal (G r)) = _
  rw [map_add, ← hcomm]
  unfold frontSpatialRemainderDuhamel frontSpatialRemainder
  change _ = (_ + _) + (A (S t.toNNReal v₀) - _ +
    ∫ r in (0 : ℝ)..t, A (S (t - r).toNNReal (G r)) -
      frontCriticalHeatEvolution f D c φ ψ h₃ (t - r).toNNReal (spatialSlices hd (G r)))
  rw [intervalIntegral.integral_sub (hAc.intervalIntegrable_of_Icc (μ := volume) ht)
    (hPc.intervalIntegrable_of_Icc (μ := volume) ht)]
  abel

end

end Planarwave
