/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontPhaseComparison
import all Planarwave.Analysis.FrontRealProfileDerivatives

/-!
# The final physical-space comparison

The last step of the paper transfers the phase estimate to the translated
front, using its bounded derivative and the inverse-modulation estimate.
The final theorem below obtains exactly the challenge's error weight and
its prescribed unforced phase. It is conditional on the tracking bounds:
local reaction--diffusion existence, the coupled nonlinear construction,
bootstrap closure and global continuation remain separate obligations.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₂

/-- The actual front has a global Lipschitz constant, supplied by its
already constructed bounded translation mode. -/
theorem lipschitzWith_front_profile :
    LipschitzWith ‖realTranslationModeBUC f D c φ ψ h₃‖₊ φ := by
  apply lipschitzWith_of_nnnorm_deriv_le (h₂.smooth.differentiable (by norm_num))
  intro z
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, realTranslationModeBUC_apply] using
    (realTranslationModeBUC f D c φ ψ h₃).norm_apply_le z

/-- Changing the phase in a translated front costs at most the bounded
profile derivative times the phase difference. -/
theorem norm_front_phase_shift_sub_le (σ τ : BUC (ℝ^(d - 1)) ℝ)
    (z : ℝ) (y : ℝ^(d - 1)) :
    ‖φ (z - σ y) - φ (z - τ y)‖ ≤
      ‖realTranslationModeBUC f D c φ ψ h₃‖ * ‖σ - τ‖ := by
  have h := (lipschitzWith_front_profile f D c φ ψ h₂ h₃).dist_le_mul (z - σ y) (z - τ y)
  have h' : ‖φ (z - σ y) - φ (z - τ y)‖ ≤
      ‖realTranslationModeBUC f D c φ ψ h₃‖ * ‖σ y - τ y‖ := by
    simpa only [dist_eq_norm, coe_nnnorm, sub_sub_sub_cancel_left, norm_sub_rev] using h
  exact h'.trans (mul_le_mul_of_nonneg_left ((σ - τ).norm_apply_le y) (norm_nonneg _))

/-- Combine the inverse-modulated perturbation and phase errors in the
original physical coordinates, without any coordinate-norm loss. -/
theorem norm_front_error_le_of_tracking_and_phase (hd : 2 ≤ d)
    (u : BUC (ℝ^d) (ℝ^n)) (b : ℝ) (σ τ : BUC (ℝ^(d - 1)) ℝ)
    {A B : ℝ} (hA : 0 ≤ A)
    (hv : ‖frontInverseModulatedPerturbation f D c φ h₂ hd u b σ‖ ≤ A)
    (hphase : ‖σ - τ‖ ≤ B) (x : ℝ^d) :
    ‖u x - φ (horizontal x - b - τ (transverse x))‖ ≤
      A + ‖realTranslationModeBUC f D c φ ψ h₃‖ * B := by
  have hphysical := (norm_frontInverseModulatedPerturbation_le_iff
    f D c φ h₂ hd u b σ hA).mp hv x
  calc
    _ ≤ ‖u x - φ (horizontal x - b - σ (transverse x))‖ +
        ‖φ (horizontal x - b - σ (transverse x)) - φ (horizontal x - b - τ (transverse x))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ A + ‖realTranslationModeBUC f D c φ ψ h₃‖ * B :=
      add_le_add hphysical ((norm_front_phase_shift_sub_le f D c φ ψ h₂ h₃ σ τ
        (horizontal x - b) (transverse x)).trans
          (mul_le_mul_of_nonneg_left hphase (norm_nonneg _)))

/-- Conditional final estimate with the exact initial phase and weight in
`vHJ_approximates_planar_front`. No extra hypothesis is added to the
challenge statement: the displayed tracking hypotheses still have to be
proved for a globally constructed reaction--diffusion solution. -/
theorem exists_front_vHJ_error_bound_of_tracking (hd : 2 ≤ d)
    {K G V : ℝ} (hK : 0 ≤ K) (hG : 0 ≤ G) (hV : 0 ≤ V) :
    ∃ C > 0, ∃ ε > 0, ∀ (T M : ℝ) (u₀ : BUC (ℝ^d) (ℝ^n))
      (u : ℝ → BUC (ℝ^d) (ℝ^n)) (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
      (ξ σ : ℝ → BUC (ℝ^(d - 1)) ℝ),
      let v₀ := frontInverseModulatedPerturbation f D c φ h₂ hd u₀ 0 0
      M ∈ Icc 0 ε → IsCloseToFront φ u₀ M →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      (∀ r ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ r) = ξ r) →
      (∀ r ∈ Icc 0 T, ‖ξ r‖ ≤ K * M) →
      (∀ r ∈ Icc 0 T, ‖frontDelayedForcing f D c φ ψ h₃ v₀ N r‖ ≤ G *
        (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) →
      (∀ r ∈ Icc 0 T,
        ‖frontInverseModulatedPerturbation f D c φ h₂ hd (u r) (c * r) (σ r)‖ ≤
          V * M / (1 + r) * Real.log (2 + r)) →
      ∀ t ∈ Icc 0 T, ∀ x,
        ‖u t x - φ (horizontal x - c * t -
          challengePhaseEvolution f D c φ ψ hd h₂ h₃ (isBUC_coe u₀) t (transverse x))‖ ≤
          C * M * (M + (1 + t)⁻¹ * Real.log (2 + t)) := by
  obtain ⟨B, hB, ε, hε, hb⟩ := exists_front_forcedPhase_comparison_bound
    (m := d - 1) f D c φ ψ h₃ hK hG
  let L := ‖realTranslationModeBUC f D c φ ψ h₃‖
  have hL : 0 ≤ L := norm_nonneg _
  let C := 1 + V + 2 * L * B
  refine ⟨C, by dsimp only [C]; positivity, ε, hε, ?_⟩
  intro T M u₀ u N ξ σ v₀ hM hclose hξ htransform hξbound hgbound hv t ht x
  have hM0 : 0 ≤ M := hM.1
  have hv₀ : ‖v₀‖ ≤ M :=
    (norm_frontInverseModulatedPerturbation_zero_le_iff f D c φ h₂ hd u₀ hM.1).mpr hclose
  have hphase := hb T M v₀ N ξ σ hM hv₀ hξ htransform hξbound hgbound t ht
  let τ := coleHopfEvolution (d_perp D φ ψ) (c / (2 * d_perp D φ ψ)) t
    (-longitudinalPairing ψ h₃.integrable v₀)
  have hτ : ∀ y, τ y = challengePhaseEvolution f D c φ ψ hd h₂ h₃ (isBUC_coe u₀) t y := by
    intro y
    unfold challengePhaseEvolution
    rw [initialPhaseBUC_eq_neg_longitudinalPairing f D c φ ψ h₃ hd h₂ u₀]
  have hden : 0 < 1 + t := by linarith [ht.1]
  have hlog : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith [ht.1])
  have hloghalf : (1 : ℝ) / 2 ≤ Real.log (2 + t) := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith [ht.1] : 2 ≤ 2 + t)
    norm_num at htwo
    linarith
  let w := M / (1 + t) * Real.log (2 + t)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hweight : M ^ 2 + M / (1 + t) ≤ 2 * (M ^ 2 + w) := by
    have h := mul_le_mul_of_nonneg_left hloghalf (div_nonneg hM0 hden.le)
    dsimp only [w]
    nlinarith [sq_nonneg M]
  have herror := norm_front_error_le_of_tracking_and_phase f D c φ ψ h₂ h₃ hd
    (u t) (c * t) (σ t) τ (by positivity : 0 ≤ V * M / (1 + t) * Real.log (2 + t))
    (hv t ht) hphase x
  rw [hτ] at herror
  calc
    _ ≤ V * M / (1 + t) * Real.log (2 + t) + L * (B * (M ^ 2 + M / (1 + t))) := herror
    _ ≤ V * w + (L * B) * (2 * (M ^ 2 + w)) := by
      have h := mul_le_mul_of_nonneg_left hweight (mul_nonneg hL hB.le)
      calc
        _ = V * w + (L * B) * (M ^ 2 + M / (1 + t)) := by dsimp only [w]; ring
        _ ≤ _ := add_le_add le_rfl h
    _ ≤ (V + 2 * L * B) * (M ^ 2 + w) := by nlinarith [mul_nonneg hV (sq_nonneg M)]
    _ ≤ C * (M ^ 2 + w) := mul_le_mul_of_nonneg_right
      (by dsimp only [C]; linarith) (add_nonneg (sq_nonneg M) hw)
    _ = _ := by dsimp only [w]; rw [div_eq_mul_inv]; ring

end

end Planarwave
