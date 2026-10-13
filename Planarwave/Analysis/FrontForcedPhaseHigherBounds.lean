/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontForcedColeHopfHigherBounds
import all Planarwave.Analysis.FrontForcedPhaseDerivativeDecay
import Planarwave.Analysis.ColeHopfInverseHigherRegularity

/-!
# Uniform higher phase bounds for the actual front

Transfer the Cole--Hopf `C^k` bound through its inverse on the small
range. Combine it with the previously constructed classical phase and
its weighted gradient and Laplacian bounds, for the same solution.
Taking `k = 9` supplies the full estimate in Step 1 of `lem:key`.
The source bootstrap is still an input, not a closed nonlinear estimate.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The actual inverse phase satisfies a uniform `C^k` bound, with a
smallness threshold independent of the horizon, data, source, and paths. -/
theorem exists_front_forced_phase_cn_bound (k : ℕ) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (ξ σ : ℝ → BUC (ℝ^m) ℝ),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      (∀ t ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) →
      ∀ t ∈ Icc 0 T,
        |c / (2 * d_perp D φ ψ)| * ‖ξ t‖ ≤ 1 / 2 ∧ BUCSpatialBound k (σ t) (C * M) := by
  obtain ⟨Cξ, hCξ, hb⟩ := exists_front_forcedColeHopf_cn_bound (m := m) f D c φ ψ h₃ k
  let β := c / (2 * d_perp D φ ψ)
  have hK : 0 < coleHopfInvSpatialConstant β Cξ k :=
    lt_of_lt_of_le (by norm_num) (two_le_coleHopfInvSpatialConstant β Cξ k)
  have hden : 0 < 2 * (|β| * Cξ + 1) := by positivity
  refine ⟨coleHopfInvSpatialConstant β Cξ k * Cξ, mul_pos hK hCξ,
    min 1 (1 / (2 * (|β| * Cξ + 1))), lt_min (by norm_num) (by positivity), ?_⟩
  intro T M v₀ N ξ σ hT hM hMM hv₀ hN hξ hCH t ht
  have hM1 : M ≤ 1 := hMM.trans (min_le_left _ _)
  have hξb := hb T M v₀ N ξ hT hM hM1 hv₀ hN hξ t ht
  have hMs : M * (2 * (|β| * Cξ + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (hMM.trans (min_le_right _ _))
  have hsmall : |β| * ‖ξ t‖ ≤ 1 / 2 := by
    have hprod := mul_le_mul_of_nonneg_left hξb.norm_le (abs_nonneg β)
    nlinarith
  refine ⟨hsmall, ?_⟩
  have heq : σ t = coleHopfInvSmallBUC β (ξ t) hsmall := by
    ext y
    rw [coleHopfInvSmallBUC_apply, ← hCH t ht, coleHopfBUC_apply]
    exact (coleHopfInv_coleHopf β (σ t y)).symm
  rw [heq]
  simpa only [mul_assoc] using hξb.coleHopfInv
    (show Cξ * M ≤ Cξ by nlinarith) hsmall

/-- Step 1 of `lem:key`, including its `C^9` portion when `k = 9`.
All spatial derivative paths of this same classical phase are BUC-continuous
in time, and the gradient/Laplacian have their weighted decay rates. -/
theorem exists_front_forced_phase_higher_and_weighted_bounds (k : ℕ) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M →
      (∀ t ∈ Icc 0 T, ‖N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC (ℝ^m) ℝ) (s : ℝ → BUC (ℝ^m) (ℝ^m)) (L : ℝ → BUC (ℝ^m) ℝ),
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T ∧
        (∀ j : ℕ, BUCSpatialRegularOn (Icc 0 T) j ξ ∧ BUCSpatialRegularOn (Icc 0 T) j σ) ∧
        ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (σ t : ℝ^m → ℝ) ∧
          BUCSpatialBound k (σ t) (C * M) ∧
          (∀ y, s t y = ∇ (σ t : ℝ^m → ℝ) y) ∧ (∀ y, L t y = Δ (σ t : ℝ^m → ℝ) y) ∧
          ‖s t‖ ≤ C * M * (1 + t) ^ (-(1 / 2 : ℝ)) ∧
          ‖L t‖ ≤ C * M * (1 + t) ^ (-(1 : ℝ)) ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * L t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  obtain ⟨Cb, hCb, Mb, hMb, hb⟩ := exists_front_forced_phase_cn_bound (m := m) f D c φ ψ h₃ k
  obtain ⟨Cw, hCw, Mw, hMw, hex⟩ :=
    exists_front_forced_phase_derivative_decay_of_source_decay (m := m) f D c φ ψ h₃
  refine ⟨Cb + Cw, by positivity, min Mb Mw, lt_min hMb hMw, ?_⟩
  intro T M v₀ N hT hM hMM hv₀ hN
  obtain ⟨ξ, σ, s, L, hξ, hσc, hsc, hLc, hσ0, hest, hPDE⟩ :=
    hex T M v₀ N hT hM (hMM.trans (min_le_right _ _)) hv₀ hN
  have hCH : ∀ t ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t :=
    fun t ht ↦ (hest t ht).2.2.2.2.2.2
  have hbound := hb T M v₀ N ξ σ hT hM (hMM.trans (min_le_left _ _)) hv₀ hN hξ hCH
  have hσinv : ∀ t ∈ Icc 0 T, ∀ y, σ t y = coleHopfInv (c / (2 * d_perp D φ ψ)) (ξ t y) := by
    intro t ht y
    rw [← hCH t ht, coleHopfBUC_apply, coleHopfInv_coleHopf]
  have hreg : ∀ j : ℕ, BUCSpatialRegularOn (Icc 0 T) j ξ ∧ BUCSpatialRegularOn (Icc 0 T) j σ := by
    intro j
    have hξreg := hξ.delayed_bucSpatialRegularOn h₃.transverse_low_wavenumber hT j
    exact ⟨hξreg, hξreg.coleHopfInv hσc (fun t ht ↦ (hbound t ht).1) hσinv⟩
  refine ⟨ξ, σ, s, L, hξ, hreg, hsc, hLc, hσ0, ?_, hPDE⟩
  intro t ht
  have hden : 0 ≤ 1 + t := by linarith [ht.1]
  obtain ⟨_, hs, hL, _, hsn, hLn, hCHt⟩ := hest t ht
  refine ⟨contDiff_infty.mpr (fun j ↦ (hreg j).2.contDiff ht),
    ((hbound t ht).2).mono (by nlinarith), hs, hL, ?_, ?_, hCHt⟩
  · exact hsn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCb.le) hM)
      (Real.rpow_nonneg hden _))
  · exact hLn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCb.le) hM)
      (Real.rpow_nonneg hden _))

/-- The summed estimate `eq:sigmafullest1` in the paper. The continuous
quantity `U` is the least common bound on the genuine spatial BUC
derivatives through order nine, so it can also be used in a bootstrap. -/
theorem exists_front_forced_phase_step_one_estimate :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ‖v₀‖ ≤ M →
      (∀ t ∈ Icc 0 T, ‖N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC (ℝ^m) ℝ) (s : ℝ → BUC (ℝ^m) (ℝ^m))
        (L : ℝ → BUC (ℝ^m) ℝ) (U : ℝ → ℝ),
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T ∧
        (∀ j : ℕ, BUCSpatialRegularOn (Icc 0 T) j ξ ∧ BUCSpatialRegularOn (Icc 0 T) j σ) ∧
        ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧ ContinuousOn U (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, BUCSpatialBound 9 (σ t) (U t) ∧
          (∀ A, BUCSpatialBound 9 (σ t) A → U t ≤ A) ∧
          (∀ y, s t y = ∇ (σ t : ℝ^m → ℝ) y) ∧ (∀ y, L t y = Δ (σ t : ℝ^m → ℝ) y) ∧
          U t + (1 + t) ^ (1 / 2 : ℝ) * ‖s t‖ + (1 + t) * ‖L t‖ ≤ C * M ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) ∧
        ∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * L t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ v₀ N t y) t := by
  obtain ⟨K, hK, μ, hμ, hex⟩ :=
    exists_front_forced_phase_higher_and_weighted_bounds (m := m) f D c φ ψ h₃ 9
  refine ⟨3 * K, by positivity, μ, hμ, ?_⟩
  intro T M v₀ N hT hM hMM hv₀ hN
  obtain ⟨ξ, σ, s, L, hξ, hreg, hsc, hLc, hσ0, hb, htime⟩ :=
    hex T M v₀ N hT hM hMM hv₀ hN
  obtain ⟨U, hUc, hU⟩ := (hreg 9).2.exists_least_bound
  refine ⟨ξ, σ, s, L, U, hξ, hreg, hsc, hLc, hUc, hσ0, ?_, htime⟩
  intro t ht
  obtain ⟨_, hσ, hs, hL, hsn, hLn, hCH⟩ := hb t ht
  have hden : 0 < 1 + t := by linarith [ht.1]
  have hUn : U t ≤ K * M := (hU t ht).2 (K * M) hσ
  have hsw : (1 + t) ^ (1 / 2 : ℝ) * ‖s t‖ ≤ K * M := by
    calc
      _ ≤ (1 + t) ^ (1 / 2 : ℝ) * (K * M * (1 + t) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsn (Real.rpow_nonneg hden.le _)
      _ = (K * M) * ((1 + t) ^ (1 / 2 : ℝ) * (1 + t) ^ (-(1 / 2 : ℝ))) := by ring
      _ = K * M := by rw [← Real.rpow_add hden, add_neg_cancel, Real.rpow_zero, mul_one]
  have hLw : (1 + t) * ‖L t‖ ≤ K * M := by
    calc
      _ ≤ (1 + t) * (K * M * (1 + t) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left hLn hden.le
      _ = (K * M) * ((1 + t) * (1 + t)⁻¹) := by rw [Real.rpow_neg_one]; ring
      _ = K * M := by rw [mul_inv_cancel₀ (ne_of_gt hden), mul_one]
  exact ⟨(hU t ht).1, (hU t ht).2, hs, hL, by nlinarith, hCH⟩

end

end Planarwave
