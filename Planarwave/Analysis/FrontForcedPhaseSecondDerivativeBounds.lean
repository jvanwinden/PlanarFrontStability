/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import all Planarwave.Analysis.FrontForcedPhaseFirstDerivativeBounds
import Planarwave.Analysis.ForcedPhaseSecondDerivativeBounds
import Planarwave.Analysis.DelayedHeatForcingSecondDerivativeBounds

/-!
# Second-order phase estimates for the actual front

Specialize the C² Cole--Hopf estimate and the actual phase Laplacian
to the original diffusivity and adjoint-projected delayed forcing.
The forcing block estimate uses only undifferentiated nonlinear data.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance frontC2TensorNormedAddCommGroup :
    NormedAddCommGroup (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) := inferInstance
local instance frontC2TensorNormedSpace : NormedSpace ℝ (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) := inferInstance
local instance frontC2BUCNormedAddCommGroup :
    NormedAddCommGroup (BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ)) := inferInstance

/-- The genuine Hessian of the front's delayed forcing. -/
def frontDelayedForcingFDeriv2 (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) :=
  delayedHeatForcingFDeriv2 h₃.transverse_low_wavenumber (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))

theorem continuous_frontDelayedForcingFDeriv2 (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) :
    Continuous (frontDelayedForcingFDeriv2 f D c φ ψ h₃ v₀ N) :=
  continuous_delayedHeatForcingFDeriv2 h₃.transverse_low_wavenumber _ _

theorem hasFDerivAt_frontDelayedForcingFDeriv (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (t : ℝ) (y : ℝ^m) :
    HasFDerivAt (frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N t)
      (frontDelayedForcingFDeriv2 f D c φ ψ h₃ v₀ N t y) y :=
  hasFDerivAt_delayedHeatForcingFDeriv h₃.transverse_low_wavenumber _ _ t y

/-- Fixed positive heat smoothing gives a C² forcing bound without
assuming any derivative bounds on the completed nonlinear source. -/
theorem norm_frontDelayedForcing_c2_block_le (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (k : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ∀ r ∈ Icc (k : ℝ) ((k : ℝ) + 1), ‖N r‖ ≤ M) :
    max ‖frontDelayedForcing f D c φ ψ h₃ v₀ N ((k : ℝ) + 1 + τ)‖
      (max ‖frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N ((k : ℝ) + 1 + τ)‖
        ‖frontDelayedForcingFDeriv2 f D c φ ψ h₃ v₀ N ((k : ℝ) + 1 + τ)‖) ≤
      trackingCutoff τ *
        (max (max 1 (heatScale (d_perp D φ ψ) (1 / 8))⁻¹) (d_perp D φ ψ * (1 / 8))⁻¹ *
          ((∫ z, ‖ψ z‖) * M)) := by
  apply norm_delayedHeatForcing_c2_block_le h₃.transverse_low_wavenumber _ _ k hτ
  intro r hr
  exact (norm_longitudinalPairing_le ψ h₃.integrable (N r)).trans
    (mul_le_mul_of_nonneg_left (hN r hr) (integral_nonneg fun z ↦ norm_nonneg (ψ z)))

/-- The actual front phase has time-continuous BUC gradient and Laplacian
with uniform second-order estimates under the paper's forcing decay input. -/
theorem exists_front_forced_phase_classical_c2 {C : ℝ} (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ →
      (∀ t ∈ Icc 0 T, max ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖
        (max ‖frontDelayedForcingFDeriv f D c φ ψ h₃ v₀ N t‖
          ‖frontDelayedForcingFDeriv2 f D c φ ψ h₃ v₀ N t‖) ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC (ℝ^m) ℝ) (q : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ))
        (h : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ))
        (s : ℝ → BUC (ℝ^m) (ℝ^m)) (L : ℝ → BUC (ℝ^m) ℝ),
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧ Continuous q ∧ Continuous h ∧
        ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : ℝ^m → ℝ) ∧
          (∀ y, HasFDerivAt (ξ t) (q t y) y ∧ HasFDerivAt (q t) (h t y) y) ∧
          (∀ y, s t y = ∇ (σ t : ℝ^m → ℝ) y) ∧ (∀ y, L t y = Δ (σ t : ℝ^m → ℝ) y) ∧
          max ‖ξ t‖ (max ‖q t‖ ‖h t‖) ≤ C₀ * M ∧ max ‖σ t‖ ‖s t‖ ≤ (2 * C₀) * M ∧
          ‖L t‖ ≤ (‖laplacianTraceCLM (E := ℝ^m) (F := ℝ)‖ *
            (2 * C₀ + 4 * |c / (2 * d_perp D φ ψ)| * C₀ ^ 2)) * M ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * L t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  have ha := h₃.transverse_low_wavenumber
  have hcancel : d_perp D φ ψ * (c / (2 * d_perp D φ ψ)) = c / 2 := by field_simp
  obtain ⟨C₀, hC₀, M₀, hM₀, hex⟩ :=
    exists_delayed_forced_phase_classical_c2 (E := ℝ^m) (c / (2 * d_perp D φ ψ)) C hC
  refine ⟨C₀, hC₀, M₀, hM₀, ?_⟩
  intro T M v₀ N hT hM hMM hdecay
  exact hex (d_perp D φ ψ) c T M (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r)) ha hcancel hT hM hMM hdecay

end

end Planarwave
