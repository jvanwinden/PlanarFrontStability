/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingBootstrapClosure
import all Planarwave.Analysis.FrontImprovedForcingDecay
import all Planarwave.Analysis.FrontForcedColeHopfHigherBounds
import all Planarwave.Analysis.FrontVHJComparison
import Planarwave.Analysis.BUCLinearPullback

/-!
# The final viscous Hamilton--Jacobi comparison on a physical tracking slab

The closed nonlinear bootstrap supplies all hypotheses of the paper's final
forced/unforced phase comparison. In particular, the improved quadratic
forcing estimate follows from the genuine physical nonlinear source, rather
than being an additional hypothesis. Constants are uniform in the horizon.
-/

open Set
open scoped Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

omit [Nontrivial (ℝ^n)] in
/-- The supplied phase gradient has a genuine time-continuous BUC derivative.
It is extracted from the phase's second spatial jet using the Riesz map. -/
theorem FrontTrackingSystem.exists_gradient_derivative {T : ℝ}
    (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T) :
    ∃ s₁ : ℝ → BUC (ℝ^(d - 1)) ((ℝ^(d - 1)) →L[ℝ] (ℝ^(d - 1))),
      ContinuousOn s₁ (Icc 0 T) ∧
        ∀ t ∈ Icc 0 T, ∀ y, HasFDerivAt (X.s t) (s₁ t y) y := by
  obtain ⟨_, q, hq, hdq⟩ := X.phase_regular
  let L := (InnerProductSpace.toDual ℝ (ℝ^(d - 1))).symm.toContinuousLinearMap
  have hsreg : BUCSpatialRegularOn (Icc 0 T) 1 X.s := (hq.postcompCLM L).congr (by
    intro t ht
    apply BUC.ext
    intro y
    rw [X.gradient_eq t ht y]
    change (InnerProductSpace.toDual ℝ (ℝ^(d - 1))).symm (q t y) =
      (InnerProductSpace.toDual ℝ (ℝ^(d - 1))).symm (fderiv ℝ (X.σ t) y)
    rw [(hdq t ht y).fderiv])
  obtain ⟨_, s₁, hs₁, hds₁⟩ := hsreg
  exact ⟨s₁, hs₁, hds₁⟩

/-- A sufficiently small physical tracking solution satisfies exactly the
challenge's error bound relative to its prescribed unforced phase. No source,
phase, forcing, or perturbation estimate is assumed, and both zero amplitude
and a zero-length time slab are included. -/
theorem exists_front_tracking_vHJ_error_bound :
    ∃ C > 0, ∃ ε > 0, ∀ {T M : ℝ}
      (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T)
      (u₀ : BUC (ℝ^d) (ℝ^n)), X.u 0 = u₀ → M ∈ Icc 0 ε →
      IsCloseToFront φ u₀ M →
      ∀ t ∈ Icc 0 T, ∀ x,
        ‖X.u t x - φ (horizontal x - c * t -
          challengePhaseEvolution f D c φ ψ hd h₂ h₃ (isBUC_coe u₀) t (transverse x))‖ ≤
          C * M * (M + (1 + t)⁻¹ * Real.log (2 + t)) := by
  obtain ⟨V, hV, εb, hεb, hclosed⟩ :=
    exists_front_tracking_bootstrap_closed f D c φ ψ h₁ h₂ h₃ hd
  obtain ⟨P, hP, εp, hεp, hphase⟩ :=
    exists_front_existing_phase_higher_and_weighted_bounds (m := d - 1) f D c φ ψ h₃ 0
  obtain ⟨J, hJ, hcole⟩ :=
    exists_front_forcedColeHopf_cn_bound (m := d - 1) f D c φ ψ h₃ 0
  let K := V + P
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hVK : V ≤ K := by dsimp [K]; linarith
  have hPK : P ≤ K := by dsimp [K]; linarith
  obtain ⟨G, hG, himproved⟩ :=
    exists_frontDelayedForcing_improved_decay (m := d - 1) f D c φ ψ h₁ h₂ h₃ hV.le hK
  obtain ⟨C, hC, εv, hεv, hfinal⟩ :=
    exists_front_vHJ_error_bound_of_tracking f D c φ ψ h₂ h₃ hd hJ.le hG.le hV.le
  refine ⟨C, hC, min εb (min εp (min 1 εv)),
    lt_min hεb (lt_min hεp (lt_min zero_lt_one hεv)), ?_⟩
  intro T M X u₀ hu₀ hM hclose
  have hM0 : 0 ≤ M := hM.1
  have hMb := hM.2.trans (min_le_left _ _)
  have hMp := hM.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hM1 : M ≤ 1 := hM.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMv : M ≤ εv := hM.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, X.nonneg⟩
  have hσzero := X.phase_initial_zero f D c φ ψ h₁ h₂ h₃ hd htzero (by norm_num)
  have hinitial : frontInverseModulatedPerturbation f D c φ h₂ hd u₀ 0 0 = X.v₀ := by
    simpa only [hu₀, hσzero, mul_zero] using X.initial
  have hv₀ : ‖X.v₀‖ ≤ M := by
    rw [← hinitial]
    exact (norm_frontInverseModulatedPerturbation_zero_le_iff
      f D c φ h₂ hd u₀ hM0).mpr hclose
  have hb : ∀ t ∈ Icc 0 T,
      ‖X.N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4) ∧
      ‖X.perturbation t‖ ≤ V * M / (1 + t) * Real.log (2 + t) := by
    rcases hM0.eq_or_lt with hzero | hpos
    · subst M
      have hvzero : X.v₀ = 0 := norm_le_zero_iff.mp hv₀
      intro t ht
      obtain ⟨_, hv, hN⟩ := X.vanish_of_initial_zero f D c φ ψ h₁ h₂ h₃ hd hvzero t ht
      simp only [hv, hN, norm_zero, mul_zero, zero_mul, zero_div, le_refl, and_self]
    · have hη := (hclosed X hpos hMb hv₀ T ⟨X.nonneg, le_rfl⟩).1
      have hN := (trackingBootstrapFunctional_le_one_bounds
        X.phase_regular.continuous X.source_continuous hpos ⟨X.nonneg, le_rfl⟩
        (hη.trans (by norm_num))).2
      exact fun t ht ↦ ⟨(hN t ht).2, (hclosed X hpos hMb hv₀ t ht).2.2.1⟩
  have hN := fun t ht ↦ (hb t ht).1
  have hv := fun t ht ↦ (hb t ht).2
  have hp := hphase T M X.v₀ X.N X.ξ X.σ X.s X.l X.nonneg hM0 hMp hv₀ hN
    X.coleHopf_mild X.coleHopf_eq X.gradient_eq X.laplacian_eq
  have hξ : ∀ t ∈ Icc 0 T, ‖X.ξ t‖ ≤ J * M :=
    fun t ht ↦ (hcole T M X.v₀ X.N X.ξ X.nonneg hM0 hM1 hv₀ hN X.coleHopf_mild t ht).norm_le
  obtain ⟨s₁, _, hds₁⟩ := X.exists_gradient_derivative f D c φ ψ h₁ h₂ h₃ hd
  have hg : ∀ t ∈ Icc 0 T, ‖X.forcing t‖ ≤
      G * (trackingCutoff t * M + M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t)) := by
    rcases X.nonneg.eq_or_lt with hzero | hpos
    · intro t ht
      have ht0 : t = 0 := by linarith [ht.1, ht.2]
      rw [(X.initial_zero ht (by rw [ht0]; norm_num)).2.2, norm_zero]
      have hcut := trackingCutoff_nonneg t
      have hlog : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith [ht.1])
      positivity
    · apply himproved T M X.v₀ X.N X.perturbation X.v₁ X.v₂
        (fun t ↦ (X.σ t : ℝ^(d - 1) → ℝ)) X.s s₁ X.l
        hpos hM0 hM1 hv₀ X.source_continuous hN
      intro t ht
      have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
      have hden : 0 < 1 + t := by linarith [ht.1]
      have hlog : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith [ht.1])
      refine ⟨X.source_eq t htc, X.first_derivative t ht, X.second_derivative t ht,
        X.gradient_eq t htc, hds₁ t htc, X.laplacian_eq t htc, ?_, ?_, ?_, ?_⟩
      · have hlogle : Real.log (2 + t) ≤ 1 + t := by
          have := Real.log_le_sub_one_of_pos (show 0 < 2 + t by linarith [ht.1])
          linarith
        calc
          ‖X.perturbation t‖ ≤ V * M / (1 + t) * Real.log (2 + t) := hv t htc
          _ ≤ V * M / (1 + t) * (1 + t) := by gcongr
          _ = V * M := div_mul_cancel₀ _ hden.ne'
          _ ≤ V := by nlinarith
      · exact (hv t htc).trans (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hVK hM0) hden.le) hlog)
      · exact (hp t htc).2.2.1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hPK hM0) (Real.rpow_nonneg hden.le _))
      · have hl := (hp t htc).2.2.2
        rw [Real.rpow_neg_one, ← div_eq_mul_inv]
        exact hl.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPK hM0) hden.le)
  apply hfinal T M u₀ X.u X.N X.ξ X.σ ⟨hM0, hMv⟩ hclose
  · simpa only [hinitial] using X.coleHopf_mild
  · exact X.coleHopf_eq
  · exact hξ
  · simpa only [hinitial, FrontTrackingSystem.forcing] using hg
  · exact hv

end

end Planarwave
