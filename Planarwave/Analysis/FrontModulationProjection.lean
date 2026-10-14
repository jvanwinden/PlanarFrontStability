/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearDispersion
import all Planarwave.Analysis.FrontModulationSource

/-!
# Cancellation in the critical projection of the full source

The normalization, transverse diffusivity, and nonlinear dispersion identity
remove both phase-derivative terms from `eq:defNtilde`. Thus the critical
heat equation is forced by precisely `⟨ψ,N⟩ - g`, as in Step 3b of `lem:key`.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- Separate a fixed longitudinal profile from its transverse coefficient. -/
theorem longitudinalPairing_profileProduct {F Y : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup Y]
    (ψ : ℝ → F) (hψ : Integrable ψ) (p : BUC ℝ F) (q : BUC Y ℝ) :
    longitudinalPairing ψ hψ (profileProduct p q) = realPairingCLM ψ hψ p • q := by
  ext y
  simp only [longitudinalPairing_apply, profileProduct_apply, inner_smul_right,
    BUC.smul_apply, smul_eq_mul, realPairingCLM_apply, integral_const_mul]
  ring

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

@[simp]
theorem realPairing_realTranslationMode :
    realPairingCLM ψ h₃.integrable (realTranslationModeBUC f D c φ ψ h₃) = 1 := by
  simpa only [realPairingCLM_apply, realTranslationModeBUC_apply] using h₃.normalized

/-- The phase-Laplacian coefficient is phase-orthogonal by definition of `d_perp`. -/
theorem realPairing_frontPhaseLaplacianProfile :
    realPairingCLM ψ h₃.integrable (frontPhaseLaplacianProfile f D c φ ψ h₃) = 0 := by
  simp only [frontPhaseLaplacianProfile, map_sub, map_smul,
    smul_eq_mul, realPairingCLM_apply, BUC.postcompCLM_apply,
    realTranslationModeBUC_apply, h₃.normalized, mul_one, d_perp, sub_self]

include h₁ h₂ in
/-- Lemma `lem:ndispersion` removes the squared-gradient coefficient. -/
theorem realPairing_frontPhaseGradientProfile :
    realPairingCLM ψ h₃.integrable (frontPhaseGradientProfile f D c φ ψ h₃) = 0 := by
  simp only [frontPhaseGradientProfile, map_add, map_smul,
    smul_eq_mul, realPairingCLM_apply, BUC.postcompCLM_apply,
    realTranslationModeDerivativeBUC_apply, realTranslationModeBUC_apply, h₃.normalized, mul_one,
    front_nonlinear_dispersion_identity f D c φ ψ h₁ h₂ h₃]
  ring

include h₁ h₂ in
/-- The exact source cancellation used in Step 3b, before any time integration. -/
theorem longitudinalPairing_frontModulationSource
    (N : BUC (ℝ^m × ℝ) (ℝ^n)) (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ) :
    longitudinalPairing ψ h₃.integrable (frontModulationSource f D c φ ψ h₃ N s l g) =
      longitudinalPairing ψ h₃.integrable N - g := by
  simp only [frontModulationSource, modulationPerturbationSource, map_sub, map_add,
    longitudinalPairing_profileProduct, realPairing_frontPhaseLaplacianProfile,
    realPairing_frontPhaseGradientProfile f D c φ ψ h₁ h₂ h₃,
    realPairing_realTranslationMode, one_smul]
  ext y
  simp only [BUC.sub_apply, BUC.add_apply, BUC.smul_apply, smul_eq_mul, zero_mul, zero_add]

include h₁ h₂ in
/-- The critical heat expression for the full source is the already
cancelled residual. Only the nonlinear source needs time-continuity;
the phase-derivative terms disappear pointwise. -/
theorem heatDuhamel_frontModulationSource_eq_trackingResidual
    (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
    (s : ℝ → BUC (ℝ^m) (ℝ^m)) (l : ℝ → BUC (ℝ^m) ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hN : ContinuousOn N (Icc 0 t)) :
    heatFlowBUC (d_perp D φ ψ) t (longitudinalPairing ψ h₃.integrable v₀) +
      heatDuhamel (d_perp D φ ψ)
        (fun r ↦ longitudinalPairing ψ h₃.integrable
          (frontModulationSource f D c φ ψ h₃ (N r) (s r) (l r)
            (frontDelayedForcing f D c φ ψ h₃ v₀ N r))) t =
      frontTrackingCriticalResidual f D c φ ψ h₃ v₀ N t := by
  simp only [longitudinalPairing_frontModulationSource f D c φ ψ h₁ h₂ h₃,
    frontTrackingCriticalResidual, heatDuhamel]
  change _ + (∫ r in (0 : ℝ)..t, (heatOperator (d_perp D φ ψ) (t - r))
    (longitudinalPairing ψ h₃.integrable (N r) - frontDelayedForcing f D c φ ψ h₃ v₀ N r)) = _
  simp only [map_sub]
  rw [intervalIntegral.integral_sub]
  · abel
  · exact ((continuous_heatFlowBUC_joint (d_perp D φ ψ)).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk
        ((longitudinalPairing ψ h₃.integrable).continuous.comp_continuousOn hN))).intervalIntegrable_of_Icc ht
  · exact ((continuous_heatDuhamel_integrand (d_perp D φ ψ)
      (continuous_frontDelayedForcing f D c φ ψ h₃ v₀ N)).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t

end

end Planarwave
