/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import all Planarwave.Analysis.FrontForcedPhaseFirstDerivativeBounds
import all Planarwave.Analysis.FrontForcedPhaseSecondDerivativeBounds
import Planarwave.Analysis.DelayedHeatForcingDecay
import Planarwave.Analysis.HeatCriticalResidualDecay

/-!
# The front's forcing and critical tracking decay

Transfer the unprojected nonlinear source bound through the actual
adjoint pairing. This gives the C² version of `eq:gest` and the decay
of the explicitly cancelled expression `eq:zeta1`. Its identification
with the full perturbation decomposition remains a separate obligation.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance frontTrackingDecayTensorNormedAddCommGroup :
    NormedAddCommGroup (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) := inferInstance
local instance frontTrackingDecayTensorNormedSpace : NormedSpace ℝ (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) := inferInstance
local instance frontTrackingDecayBUCNormedAddCommGroup :
    NormedAddCommGroup (BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ)) := inferInstance

/-- A positive decay constant depending only on the front and exponent. -/
def frontForcingC2DecayConstant (γ : ℝ) : ℝ :=
  delayedForcingC2DecayConstant (d_perp D φ ψ) γ * (∫ z, ‖ψ z‖) + 1

theorem frontForcingC2DecayConstant_pos (γ : ℝ) : 0 < frontForcingC2DecayConstant D φ ψ γ := by
  have hA : 0 ≤ ∫ z, ‖ψ z‖ := integral_nonneg fun z ↦ norm_nonneg (ψ z)
  have hC := delayedForcingC2DecayConstant_pos (d_perp D φ ψ) γ
  unfold frontForcingC2DecayConstant
  positivity

/-- The actual forcing inherits polynomial decay from the unprojected
source, through order two, without any source derivative assumptions. -/
theorem norm_frontDelayedForcing_c2_decay_le {γ T M t : ℝ} (hγ : 0 ≤ γ)
    (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
    (hM : 0 ≤ M) (hv₀ : ‖v₀‖ ≤ M)
    (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ)) (ht : t ∈ Icc 0 T) :
    max ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖
      (max ‖frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N t‖
        ‖frontDelayedForcingFDeriv2 f D c φ ψ h₃ v₀ N t‖) ≤
      frontForcingC2DecayConstant D φ ψ γ * M * (1 + t) ^ (-γ) := by
  let A := ∫ z, ‖ψ z‖
  have hA : 0 ≤ A := integral_nonneg fun z ↦ norm_nonneg (ψ z)
  have hp : ‖longitudinalPairing ψ h₃.integrable v₀‖ ≤ A * M :=
    (norm_longitudinalPairing_le ψ h₃.integrable v₀).trans (mul_le_mul_of_nonneg_left hv₀ hA)
  have hproj : ∀ r ∈ Icc 0 T, ‖longitudinalPairing ψ h₃.integrable (N r)‖ ≤
      (A * M) * (1 + r) ^ (-γ) := by
    intro r hr
    calc
      _ ≤ A * ‖N r‖ := norm_longitudinalPairing_le ψ h₃.integrable (N r)
      _ ≤ A * (M * (1 + r) ^ (-γ)) := mul_le_mul_of_nonneg_left (hN r hr) hA
      _ = _ := by ring
  have hb := norm_delayedHeatForcing_c2_decay_le h₃.transverse_low_wavenumber hγ
    (longitudinalPairing ψ h₃.integrable v₀) (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))
    (mul_nonneg hA hM) hp hproj ht
  apply hb.trans
  calc
    _ = (delayedForcingC2DecayConstant (d_perp D φ ψ) γ * A) * M * (1 + t) ^ (-γ) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hM)
        (Real.rpow_nonneg (by linarith [ht.1]) _)
      change _ ≤ delayedForcingC2DecayConstant (d_perp D φ ψ) γ * A + 1
      linarith

/-- The cancelled critical heat expression `eq:zeta1` for the original
front coefficients and the actual adjoint projection. -/
def frontTrackingCriticalResidual (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (t : ℝ) : BUC (ℝ^m) ℝ :=
  heatFlowBUC (d_perp D φ ψ) t (longitudinalPairing ψ h₃.integrable v₀) +
    heatDuhamel (d_perp D φ ψ) (fun r ↦ longitudinalPairing ψ h₃.integrable (N r)) t -
    heatDuhamel (d_perp D φ ψ) (frontDelayedForcing f D c φ ψ h₃ v₀ N) t

/-- The critical tracking expression inherits the decay exponent of the
unprojected source, with the constant fixed before all paths and times. -/
theorem norm_frontTrackingCriticalResidual_decay_le {γ T M t : ℝ} (hγ : 0 ≤ γ)
    (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
    (hM : 0 ≤ M) (hv₀ : ‖v₀‖ ≤ M) (hNc : ContinuousOn N (Icc 0 T))
    (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ)) (ht : t ∈ Icc 0 T) :
    ‖frontTrackingCriticalResidual f D c φ ψ h₃ v₀ N t‖ ≤
      (3 * (3 : ℝ) ^ γ * (∫ z, ‖ψ z‖)) * M * (1 + t) ^ (-γ) := by
  let A := ∫ z, ‖ψ z‖
  have hA : 0 ≤ A := integral_nonneg fun z ↦ norm_nonneg (ψ z)
  have hp : ‖longitudinalPairing ψ h₃.integrable v₀‖ ≤ A * M :=
    (norm_longitudinalPairing_le ψ h₃.integrable v₀).trans (mul_le_mul_of_nonneg_left hv₀ hA)
  have hproj : ∀ r ∈ Icc 0 T, ‖longitudinalPairing ψ h₃.integrable (N r)‖ ≤
      (A * M) * (1 + r) ^ (-γ) := by
    intro r hr
    calc
      _ ≤ A * ‖N r‖ := norm_longitudinalPairing_le ψ h₃.integrable (N r)
      _ ≤ A * (M * (1 + r) ^ (-γ)) := mul_le_mul_of_nonneg_left (hN r hr) hA
      _ = _ := by ring
  calc
    _ ≤ (3 * (3 : ℝ) ^ γ) * (A * M) * (1 + t) ^ (-γ) :=
      norm_heatCriticalResidual_decay_le h₃.transverse_low_wavenumber.le hγ _ _ (mul_nonneg hA hM) hp
        ((longitudinalPairing ψ h₃.integrable).continuous.comp_continuousOn hNc) hproj ht
    _ = _ := by ring

end

end Planarwave
