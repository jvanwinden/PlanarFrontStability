/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import Planarwave.Analysis.DelayedHeatForcingHigherDerivativeBounds

/-!
# The actual front forcing has all-order spatial decay

The unprojected source bootstrap implies `eq:gest`, including order nine.
The adjoint pairing and diffusivity are exactly those of the challenge.
The constant is selected before the initial datum, source, time horizon,
smallness parameter, time, and derivative fields. No derivative of `N`
is assumed. This is an a priori estimate for the supplied source, not yet
construction or closure of the coupled nonlinear tracking solution.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance frontHigherTensorNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup ((ℝ^m) [×k]→L[ℝ] ℝ) := inferInstance
local instance frontHigherTensorNormedSpace (k : ℕ) :
    NormedSpace ℝ ((ℝ^m) [×k]→L[ℝ] ℝ) := inferInstance
local instance frontHigherBUCNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (BUC (ℝ^m) ((ℝ^m) [×k]→L[ℝ] ℝ)) := inferInstance

/-- The paper's forcing decay in `C^K`, as actual BUC spatial derivatives.
Taking `K = 9` and `γ = 5/4` gives the estimate needed in Step 1 of `lem:key`. -/
theorem exists_frontDelayedForcing_cn_decay (K : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ C > 0, ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
      (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)),
      0 ≤ M → ‖v₀‖ ≤ M →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ)) →
      ∀ t ∈ Icc 0 T, ∀ k ≤ K,
        ∃ g : BUC (ℝ^m) ((ℝ^m) [×k]→L[ℝ] ℝ),
          (∀ y, g y = iteratedFDeriv ℝ k
            (frontDelayedForcing f D c φ ψ h₃ v₀ N t : ℝ^m → ℝ) y) ∧
          ‖g‖ ≤ C * M * (1 + t) ^ (-γ) := by
  let P := ∫ z, ‖ψ z‖
  have hP : 0 ≤ P := integral_nonneg fun z ↦ norm_nonneg (ψ z)
  let H := ‖trackingCutoff‖ * delayedForcingSpatialConstant (d_perp D φ ψ) K * (3 : ℝ) ^ γ
  have hH : 0 ≤ H := mul_nonneg
    (mul_nonneg (norm_nonneg _) (delayedForcingSpatialConstant_pos _ _).le)
    (Real.rpow_nonneg (by norm_num) _)
  refine ⟨H * P + 1, by positivity, ?_⟩
  intro T M v₀ N hM hv₀ hN t ht k hk
  have hp : ‖longitudinalPairing ψ h₃.integrable v₀‖ ≤ P * M :=
    (norm_longitudinalPairing_le ψ h₃.integrable v₀).trans (mul_le_mul_of_nonneg_left hv₀ hP)
  have hproj : ∀ r ∈ Icc 0 T, ‖longitudinalPairing ψ h₃.integrable (N r)‖ ≤
      (P * M) * (1 + r) ^ (-γ) := by
    intro r hr
    calc
      _ ≤ P * ‖N r‖ := norm_longitudinalPairing_le ψ h₃.integrable (N r)
      _ ≤ P * (M * (1 + r) ^ (-γ)) := mul_le_mul_of_nonneg_left (hN r hr) hP
      _ = _ := by ring
  obtain ⟨g, hg, hbound⟩ := exists_buc_iteratedFDeriv_delayedHeatForcing
    h₃.transverse_low_wavenumber hγ K k hk
    (longitudinalPairing ψ h₃.integrable v₀) (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))
    (mul_nonneg hP hM) hp hproj ht
  refine ⟨g, hg, ?_⟩
  calc
    ‖g‖ ≤ H * (P * M) * (1 + t) ^ (-γ) := hbound
    _ = (H * P) * M * (1 + t) ^ (-γ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : H * P ≤ H * P + 1) hM)
      (Real.rpow_nonneg (by linarith [ht.1]) _)

end

end Planarwave
