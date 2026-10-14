/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSmoothedNonlinearityDecay
import all Planarwave.Analysis.FrontTrackingDecay
import Planarwave.Analysis.DelayedHeatForcingImprovedDecay

/-!
# The improved forcing bound for the actual nonlinear tracking source

The `k = 0` case of `eq:gbetterest`, following Step 5 of `lem:key`.
Use Lemma 4.2 for the exact inverse-modulation nonlinearity, then transfer
the smoothed estimate through the actual delayed forcing. The old linear
forcing estimate is derived internally from the bootstrap source bound.
All spatial derivative witnesses are required only at positive times.
-/

open MeasureTheory Set
open scoped Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- Transfer a smoothed-source bound to the actual adjoint-projected forcing. -/
theorem norm_frontDelayedForcing_improved_le {A T : ℝ} (hA : 0 ≤ A)
    (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
    (hN : ContinuousOn N (Icc 0 T))
    (hb : ∀ r ∈ Icc 0 T,
      ‖heatFlowBUC (d_perp D φ ψ) (1 / 8) (longitudinalPairing ψ h₃.integrable (N r))‖ ≤
        A * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖ ≤
      trackingCutoff t * (∫ z, ‖ψ z‖) * ‖v₀‖ +
        (‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2)) * A *
          (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) := by
  have h := norm_delayedHeatForcing_improved_decay_le h₃.transverse_low_wavenumber.le
    (by norm_num : (0 : ℝ) ≤ 3 / 2) hA
    (longitudinalPairing ψ h₃.integrable v₀) (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))
    ((longitudinalPairing ψ h₃.integrable).continuous.comp_continuousOn hN)
    (by simpa only [neg_div] using hb) ht
  apply h.trans
  apply add_le_add _ (by simp only [neg_div]; exact le_rfl)
  calc
    _ ≤ trackingCutoff t * ((∫ z, ‖ψ z‖) * ‖v₀‖) :=
      mul_le_mul_of_nonneg_left (norm_longitudinalPairing_le ψ h₃.integrable v₀) (trackingCutoff_nonneg t)
    _ = _ := by ring

/-- The quadratic improved forcing bound for the actual nonlinearity.
The source bootstrap and low-order phase/tracking estimates are the inputs;
neither an improved source projection nor a forcing bound is assumed. -/
theorem exists_frontDelayedForcing_improved_decay {R K : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K) :
    ∃ C > 0, ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
      (N v : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
      (v₁ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
      (v₂ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
      (σ : ℝ → ℝ^m → ℝ) (s : ℝ → BUC (ℝ^m) (ℝ^m))
      (s₁ : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m)) (l : ℝ → BUC (ℝ^m) ℝ),
      0 < T → 0 ≤ M → M ≤ 1 → ‖v₀‖ ≤ M → ContinuousOn N (Icc 0 T) →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      (∀ r ∈ Ioc 0 T,
        N r = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ (v r) (v₁ r) (v₂ r)
          (s r) (l r) (frontDelayedForcing f D c φ ψ h₃ v₀ N r) ∧
        (∀ x, HasFDerivAt (v r) (v₁ r x) x) ∧ (∀ x, HasFDerivAt (v₁ r) (v₂ r x) x) ∧
        (∀ y, s r y = ∇ (σ r) y) ∧ (∀ y, HasFDerivAt (s r) (s₁ r y) y) ∧
        (∀ y, l r y = Δ (σ r) y) ∧ ‖v r‖ ≤ R ∧
        ‖v r‖ ≤ K * M / (1 + r) * Real.log (2 + r) ∧
        ‖s r‖ ≤ K * M * (1 + r) ^ (-(1 / 2 : ℝ)) ∧
        ‖l r‖ ≤ K * M * (1 + r) ^ (-(1 : ℝ))) →
      ∀ t ∈ Icc 0 T, ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖ ≤
        C * (trackingCutoff t * M + M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t)) := by
  let K' := max K (frontForcingC2DecayConstant D φ ψ (5 / 4))
  have hK' : 0 ≤ K' := hK.trans (le_max_left _ _)
  obtain ⟨B, hB, hb⟩ := exists_frontSmoothedNonlinearity_decay (m := m) f D c φ ψ h₁ h₂ h₃ hR hK'
  let P := ∫ z, ‖ψ z‖
  have hP : 0 ≤ P := integral_nonneg fun z ↦ norm_nonneg (ψ z)
  let Q := ‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2) * B
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let C := P + Q + 1
  have hPC : P ≤ C := by dsimp only [C]; linarith
  have hQC : Q ≤ C := by dsimp only [C]; linarith
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T M v₀ N v v₁ v₂ σ s s₁ l hT hM hM1 hv₀ hNc hN hdata t ht
  have hsm : ∀ r ∈ Icc 0 T,
      ‖heatFlowBUC (d_perp D φ ψ) (1 / 8) (longitudinalPairing ψ h₃.integrable (N r))‖ ≤
        (B * M ^ 2) * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r) := by
    apply frontSmoothedSource_decay_at_zero f D c φ ψ h₃ hT N hNc
    intro r hr
    obtain ⟨hNr, hv₁, hv₂, hsid, hs₁, hlid, hvR, hv, hs, hl⟩ := hdata r hr
    have hden : 0 ≤ 1 + r := by linarith [hr.1]
    have hKM : K * M ≤ K' * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    have hg : ‖frontDelayedForcing f D c φ ψ h₃ v₀ N r‖ ≤
        K' * M * (1 + r) ^ (-(5 : ℝ) / 4) := by
      apply (le_max_left _ _).trans
      apply (norm_frontDelayedForcing_c2_decay_le f D c φ ψ h₃
        (by norm_num : (0 : ℝ) ≤ 5 / 4) v₀ N hM hv₀
        (by simpa only [neg_div] using hN) ⟨hr.1.le, hr.2⟩).trans
      simpa only [neg_div] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right K (frontForcingC2DecayConstant D φ ψ (5 / 4))) hM)
        (Real.rpow_nonneg hden (-(5 : ℝ) / 4))
    rw [hNr]
    exact hb M r (v r) (v₁ r) (v₂ r) (σ r) (s r) (s₁ r) (l r)
      (frontDelayedForcing f D c φ ψ h₃ v₀ N r) hM hM1 hr.1.le hv₁ hv₂ hsid hs₁ hlid hvR
      (hv.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hKM hden)
        (Real.log_nonneg (by linarith [hr.1]))))
      (hs.trans (mul_le_mul_of_nonneg_right hKM (Real.rpow_nonneg hden _)))
      (hl.trans (mul_le_mul_of_nonneg_right hKM (Real.rpow_nonneg hden _))) hg
  have hforce := norm_frontDelayedForcing_improved_le f D c φ ψ h₃ (mul_nonneg hB.le (sq_nonneg M)) v₀ N hNc hsm ht
  have hweight : 0 ≤ M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) :=
    mul_nonneg (mul_nonneg (sq_nonneg M) (Real.rpow_nonneg (by linarith [ht.1]) _))
      (Real.log_nonneg (by linarith [ht.1]))
  calc
    _ ≤ trackingCutoff t * P * ‖v₀‖ +
        (‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2)) * (B * M ^ 2) *
          (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) := hforce
    _ ≤ trackingCutoff t * P * M +
        (‖trackingCutoff‖ * (3 : ℝ) ^ ((3 : ℝ) / 2)) * (B * M ^ 2) *
          (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) :=
      add_le_add (mul_le_mul_of_nonneg_left hv₀ (mul_nonneg (trackingCutoff_nonneg t) hP)) le_rfl
    _ = P * (trackingCutoff t * M) + Q * (M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t)) := by
      dsimp only [Q]; ring
    _ ≤ C * (trackingCutoff t * M) + C * (M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t)) :=
      add_le_add (mul_le_mul_of_nonneg_right hPC (mul_nonneg (trackingCutoff_nonneg t) hM))
        (mul_le_mul_of_nonneg_right hQC hweight)
    _ = _ := by ring

end

end Planarwave
