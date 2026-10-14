/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingSystem
import all Planarwave.Analysis.FrontExistingPhaseBounds
import all Planarwave.Analysis.FrontPhysicalModulationBounds
import all Planarwave.Analysis.FrontPhysicalNormBound
import all Planarwave.Analysis.FrontCutoffNonlinearityDecay
import Planarwave.Analysis.TrackingSmoothingCutoff

/-!
# The improved source estimate for the coupled physical tracking equations

Combine Steps 1--5 of the paper's a priori argument for the same physical
solution: phase bounds, logarithmic tracking, physical parabolic smoothing,
inverse modulation, interpolation, and the nonlinear power count. The
result improves the assumed source bound by a factor `M^(3/4)`.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- The phase, physical perturbation, and nonlinear source estimates of
the nonlinear iteration. No physical norm bound or derivative bound is
assumed. All constants precede the amplitude, horizon, and solution. -/
theorem exists_front_tracking_apriori :
    ∃ C > 0, ∃ ε > 0, ∀ {T M : ℝ},
      ∀ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T,
      0 ≤ M → M ≤ ε → ‖X.v₀‖ ≤ M →
      (∀ r ∈ Icc 0 T, ‖X.N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      ∀ t ∈ Icc 0 T,
        ‖X.σ t‖ ≤ C * M ∧
        ‖X.perturbation t‖ ≤ C * M / (1 + t) * Real.log (2 + t) ∧
        ‖X.N t‖ ≤ C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
  obtain ⟨P, hP, μ, hμ, hphase⟩ :=
    exists_front_existing_phase_higher_and_weighted_bounds (m := d - 1) f D c φ ψ h₃ 9
  obtain ⟨V, hV, htrack⟩ := exists_front_physical_tracking_decay f D c φ ψ h₁ h₂ h₃ hd P
  let G := frontForcingC2DecayConstant D φ ψ (5 / 4)
  have hG : 0 < G := frontForcingC2DecayConstant_pos D φ ψ (5 / 4)
  let K := P + V + G
  have hK : 0 < K := by dsimp [K]; positivity
  have hPK : P ≤ K := by dsimp [K]; linarith
  have hVK : V ≤ K := by dsimp [K]; linarith
  have hGK : G ≤ K := by dsimp [K]; linarith
  let B := V + ‖frontSplitProfileBUC (m := d - 1) f D c φ h₂‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨H, hH, ν, hν, hsmooth⟩ :=
    exists_front_physical_modulated_cutoff_c2_decay f D c φ ψ h₁ h₂ h₃ hd
      (δ := 1 / 8) (by norm_num) hB hK.le
  obtain ⟨A, hA, hnonlin⟩ := exists_front_cutoff_nonlinearity_decay
    (m := d - 1) f D c φ ψ h₁ h₂ hK.le hH.le
  let C := P + V + A
  have hPC : P ≤ C := by dsimp [C]; linarith
  have hVC : V ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, min μ (min ν 1),
    lt_min hμ (lt_min hν zero_lt_one), ?_⟩
  intro T M X hM hMε hv₀ hN
  have hMμ := hMε.trans (min_le_left _ _)
  have hMν := hMε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hM1 : M ≤ 1 := hMε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp := hphase T M X.v₀ X.N X.ξ X.σ X.s X.l X.nonneg hM hMμ hv₀ hN
    X.coleHopf_mild X.coleHopf_eq X.gradient_eq X.laplacian_eq
  have hs : ∀ r ∈ Icc 0 T, ‖X.s r‖ ≤ P * M * (1 + r) ^ (-(1 / 2 : ℝ)) :=
    fun r hr ↦ (hp r hr).2.2.1
  have hl : ∀ r ∈ Icc 0 T, ‖X.l r‖ ≤ P * M * (1 + r) ^ (-(1 : ℝ)) := by
    intro r hr
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using (hp r hr).2.2.2
  have hv : ∀ r ∈ Icc 0 T, ‖X.perturbation r‖ ≤ V * M / (1 + r) * Real.log (2 + r) :=
    htrack T M X.u X.σ X.v₀ X.N X.s X.l X.v₁ X.v₂ X.nonneg hM hM1
      X.physical_continuous X.physical_mild X.phase_regular.continuous
      (X.phase_regular.mono Ioo_subset_Icc_self) X.source_continuous
      X.gradient_continuous X.laplacian_continuous X.initial hv₀
      (fun r hr ↦ X.gradient_eq r (Ioo_subset_Icc_self hr))
      (fun r hr ↦ X.laplacian_eq r (Ioo_subset_Icc_self hr)) X.phase_pde
      (fun r hr ↦ X.first_derivative r ⟨hr.1, hr.2.le⟩)
      (fun r hr ↦ X.second_derivative r ⟨hr.1, hr.2.le⟩)
      (fun r hr ↦ X.source_eq r (Ioo_subset_Icc_self hr)) hN hs hl
  have hvK : ∀ r ∈ Icc 0 T, ‖X.perturbation r‖ ≤ K * M / (1 + r) * Real.log (2 + r) := by
    intro r hr
    apply (hv r hr).trans
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hVK hM)
        (by linarith [hr.1])) (Real.log_nonneg (by linarith [hr.1]))
  have hub : ∀ r ∈ Icc 0 T, ‖X.u r‖ ≤ B := by
    intro r hr
    have hlog : Real.log (2 + r) ≤ 1 + r := by
      have := Real.log_le_sub_one_of_pos (show 0 < 2 + r by linarith [hr.1])
      linarith
    have hvV : ‖X.perturbation r‖ ≤ V := by
      apply (hv r hr).trans
      calc
        _ ≤ V * M / (1 + r) * (1 + r) :=
          mul_le_mul_of_nonneg_left hlog
            (div_nonneg (mul_nonneg hV.le hM) (by linarith [hr.1]))
        _ = V * M := div_mul_cancel₀ _ (by linarith [hr.1])
        _ ≤ V := by nlinarith
    exact (norm_le_frontInverseModulatedPerturbation_add_profile f D c φ h₂ hd
      (X.u r) (c * r) (X.σ r)).trans (add_le_add hvV le_rfl)
  have hc2 := hsmooth T M X.u X.v₀ X.N X.ξ X.σ X.nonneg hM hMν
    X.physical_continuous hub X.physical_mild hv₀ hN X.coleHopf_mild X.coleHopf_eq
    trackingSmoothingCutoff (fun r hr ↦ trackingSmoothingCutoff_zero hr.le)
    abs_trackingSmoothingCutoff_le_one
  intro t ht
  refine ⟨(hp t ht).2.1.trans (mul_le_mul_of_nonneg_right hPC hM), ?_, ?_⟩
  · apply (hv t ht).trans
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hVC hM)
        (by linarith [ht.1])) (Real.log_nonneg (by linarith [ht.1]))
  · have hsK : ‖X.s t‖ ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)) := by
      apply (hs t ht).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPK hM)
        (Real.rpow_nonneg (by linarith [ht.1]) _)
    have hlK : ‖X.l t‖ ≤ K * M * (1 + t) ^ (-(1 : ℝ)) := by
      apply (hl t ht).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPK hM)
        (Real.rpow_nonneg (by linarith [ht.1]) _)
    have hgK : ‖X.forcing t‖ ≤ K * M * (1 + t) ^ (-(5 : ℝ) / 4) := by
      have hg : ‖X.forcing t‖ ≤ G * M * (1 + t) ^ (-(5 : ℝ) / 4) := by
        simpa only [neg_div, FrontTrackingSystem.forcing, G] using! (le_max_left _ _).trans
          (norm_frontDelayedForcing_c2_decay_le f D c φ ψ h₃
            (by norm_num : (0 : ℝ) ≤ 5 / 4) X.v₀ X.N hM hv₀
            (by simpa only [neg_div] using hN) ht)
      apply hg.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGK hM)
        (Real.rpow_nonneg (by linarith [ht.1]) _)
    have hn := hnonlin hM hM1 ht.1 (X.perturbation t) (X.v₁ t) (X.v₂ t)
      (X.s t) (X.l t) (X.forcing t) (hvK t ht) hsK hlK hgK (X.initial_zero ht) (fun hlate ↦ ?_)
    · rw [X.source_eq t ht]
      exact hn.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hM _))
        (Real.rpow_nonneg (by linarith [ht.1]) _))
    · refine ⟨?_, X.first_derivative t ⟨by linarith, ht.2⟩,
        X.second_derivative t ⟨by linarith, ht.2⟩⟩
      simpa only [trackingSmoothingCutoff_one hlate.le, one_smul] using! hc2 t ht (hvK t ht)

end

end Planarwave
