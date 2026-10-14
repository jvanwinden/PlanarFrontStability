/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingSystem
import all Planarwave.Analysis.FrontDelayedForcingCausality
import all Planarwave.Analysis.FrontForcedPhaseHigherBounds

/-!
# Extending the tracking phase to the next unit block

The old nonlinear source on `[0,k]` determines the delayed forcing through
time `k+1`. Extend that source by zero only for the phase existence argument;
causality identifies the resulting forcing with the original forcing on
the whole new slab. Uniqueness then identifies the new phase and its actual
derivatives with the old ones. No bound on the future true source is assumed.
-/

open Set
open scoped Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ}
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- A bootstrap bound on the old nonlinear source suffices to extend the
phase, with all of its genuine derivative data, through the next unit block.
The equation on the enlarged slab uses the original source's forcing. -/
theorem exists_frontTrackingPhaseExtension :
    ∃ ε > 0, ∀ (k : ℕ) (T M : ℝ)
      (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd (k : ℝ)),
      (k : ℝ) ≤ T → T ≤ (k : ℝ) + 1 → 0 ≤ M → M ≤ ε → ‖X.v₀‖ ≤ M →
      (∀ t ∈ Icc 0 (k : ℝ), ‖X.N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ (ξ σ : ℝ → BUC (ℝ^(d - 1)) ℝ)
        (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (L : ℝ → BUC (ℝ^(d - 1)) ℝ),
        IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
          (frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N) ξ T ∧
        (∀ j : ℕ, BUCSpatialRegularOn (Icc 0 T) j ξ ∧ BUCSpatialRegularOn (Icc 0 T) j σ) ∧
        ContinuousOn s (Icc 0 T) ∧ ContinuousOn L (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T,
          (∀ y, s t y = ∇ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          (∀ y, L t y = Δ (σ t : ℝ^(d - 1) → ℝ) y) ∧
          coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) ∧
        (∀ t ∈ Ioo 0 T, ∀ y, HasDerivAt (fun r ↦ σ r y)
          (d_perp D φ ψ * L t y + (c / 2) * ‖s t y‖ ^ 2 -
            frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N t y) t) ∧
        EqOn ξ X.ξ (Icc 0 (k : ℝ)) ∧ EqOn σ X.σ (Icc 0 (k : ℝ)) ∧
        EqOn s X.s (Icc 0 (k : ℝ)) ∧ EqOn L X.l (Icc 0 (k : ℝ)) := by
  obtain ⟨_, _, ε, hε, hex⟩ :=
    exists_front_forced_phase_higher_and_weighted_bounds (m := d - 1) f D c φ ψ h₃ 2
  refine ⟨ε, hε, ?_⟩
  intro k T M X hkT hTk hM hMε hv₀ hN
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hT : 0 ≤ T := hk.trans hkT
  have hNpast : ∀ t ∈ Icc 0 T,
      ‖trackingPastSource X.N k t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4) := by
    intro t ht
    simpa only [neg_div] using norm_trackingPastSource_le (γ := (5 : ℝ) / 4)
      hM (by simpa only [neg_div] using hN) ht.1
  obtain ⟨ξ, σ, s, L, hξ, hreg, hsc, hLc, hσ0, hb, hPDE⟩ :=
    hex T M X.v₀ (trackingPastSource X.N k) hT hM hMε hv₀ hNpast
  have hg : EqOn (frontDelayedForcing f D c φ ψ h₃ X.v₀ (trackingPastSource X.N k))
      (frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N) (Icc 0 T) := by
    intro t ht
    exact frontDelayedForcing_trackingPastSource f D c φ ψ h₃ X.v₀ X.N k
      (ht.2.trans hTk)
  have hξorig := hξ.congr_forcing hg
  have hξeq : EqOn ξ X.ξ (Icc 0 (k : ℝ)) :=
    (hξorig.mono hkT).unique X.coleHopf_mild
      (continuous_frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N).continuousOn hk
  have hσeq : EqOn σ X.σ (Icc 0 (k : ℝ)) := by
    intro t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hkT⟩
    ext y
    apply (strictMono_coleHopf (c / (2 * d_perp D φ ψ))).injective
    have heq : coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) =
        coleHopfBUC (c / (2 * d_perp D φ ψ)) (X.σ t) := by
      rw [(hb t htT).2.2.2.2.2.2, X.coleHopf_eq t ht, hξeq ht]
    exact congrArg (fun v : BUC (ℝ^(d - 1)) ℝ ↦ v y) heq
  refine ⟨ξ, σ, s, L, hξorig, hreg, hsc, hLc, hσ0, ?_, ?_, hξeq, hσeq, ?_, ?_⟩
  · intro t ht
    exact ⟨(hb t ht).2.2.1, (hb t ht).2.2.2.1, (hb t ht).2.2.2.2.2.2⟩
  · intro t ht y
    simpa only [hg ⟨ht.1.le, ht.2.le⟩] using hPDE t ht y
  · intro t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hkT⟩
    ext y
    rw [(hb t htT).2.2.1 y, hσeq ht, X.gradient_eq t ht y]
  · intro t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hkT⟩
    ext y
    rw [(hb t htT).2.2.2.1 y, hσeq ht, X.laplacian_eq t ht y]

end

end Planarwave
