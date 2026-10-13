/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfClassical

@[expose] public section

/-!
# The classical forced phase from the constructed Cole--Hopf solution

Apply the inverse transform to the actual delayed-forcing solution. The
small-range bound and the cancellation `a * β = c / 2` give the forced
viscous Hamilton--Jacobi equation as in the last part of `lem:xiAP`.
This proves C² spatial regularity and the classical time equation, not
yet the paper's arbitrary-order smoothness and C^k estimates.
-/

open Set Filter
open scoped Topology ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Spatial C² regularity survives the inverse transform throughout the
small range used in the paper. -/
theorem contDiff_two_coleHopfInv_of_small {β : ℝ} {ξ : BUC E ℝ}
    (hξ : ContDiff ℝ 2 (ξ : E → ℝ)) (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) :
    ContDiff ℝ 2 (coleHopfInv β ∘ ξ) := by
  rw [← contDiffOn_univ]
  apply ((contDiffOn_coleHopfInv β).of_le (show (2 : ℕ∞ω) ≤ ∞ from
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).comp hξ.contDiffOn
  intro x _
  exact Icc_subset_coleHopfDomain_of_small_radius hsmall (abs_le.mp (ξ.norm_apply_le x))

/-- The inverse of the constructed delayed solution satisfies the
forced viscous Hamilton--Jacobi equation at every interior time. -/
theorem IsForcedColeHopfMild.delayed_inverse_hasDerivAt {a β c T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hcancel : a * β = c / 2) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hsmall : |β| * ‖ξ t‖ ≤ 1 / 2) (x : E) :
    HasDerivAt (fun r ↦ coleHopfInv β (ξ r x))
      (a * Δ (coleHopfInv β ∘ ξ t) x +
        (c / 2) * ‖∇ (coleHopfInv β ∘ ξ t) x‖ ^ 2 - delayedHeatForcing a p N t x) t :=
  hasDerivAt_coleHopfInv_of_forced_heat (fun r x ↦ ξ r x) t x a c β
    (delayedHeatForcing a p N t x) (hξ.delayed_hasDerivAt ha ht x)
    (hξ.delayed_contDiff_two ha (ht.1.trans ht.2).le ⟨ht.1.le, ht.2.le⟩)
    (fun y ↦ Icc_subset_coleHopfDomain_of_small_radius hsmall
      (abs_le.mp ((ξ t).norm_apply_le y))) hcancel

/-- A BUC realization of the inverse phase is genuinely classical;
agreement with the inverse is only required on the time interval. -/
theorem IsForcedColeHopfMild.delayed_phase_classical {a β c T : ℝ}
    {p : BUC E ℝ} {N ξ σ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) (hcancel : a * β = c / 2)
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hσ : ∀ t ∈ Icc 0 T, ∀ x, σ t x = coleHopfInv β (ξ t x)) :
    (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : E → ℝ)) ∧
      ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r ↦ σ r x)
        (a * Δ (σ t : E → ℝ) x + (c / 2) * ‖∇ (σ t : E → ℝ) x‖ ^ 2 -
          delayedHeatForcing a p N t x) t := by
  have heq : ∀ t ∈ Icc 0 T, (σ t : E → ℝ) = coleHopfInv β ∘ ξ t :=
    fun t ht ↦ funext (hσ t ht)
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [heq t ht]
    exact contDiff_two_coleHopfInv_of_small (hξ.delayed_contDiff_two ha hT ht) (hsmall t ht)
  · intro t ht x
    rw [heq t ⟨ht.1.le, ht.2.le⟩]
    apply (hξ.delayed_inverse_hasDerivAt ha hcancel ht (hsmall t ⟨ht.1.le, ht.2.le⟩) x).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    exact hσ r hr x

/-- Classical delayed forced-phase existence and the uniform zero-order
estimate of `lem:xiAP`. Constants are chosen before the final time and
source. The supplied source still has to be closed by the tracking argument. -/
theorem exists_delayed_forced_phase_classical (β C : ℝ) (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0, ∀ (a c T M : ℝ) (p : BUC E ℝ) (N : ℝ → BUC E ℝ),
      0 < a → a * β = c / 2 → 0 ≤ T → 0 ≤ M → M ≤ M₀ →
      (∀ t ∈ Icc 0 T, ‖delayedHeatForcing a p N t‖ ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ ξ σ : ℝ → BUC E ℝ,
        IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧
        ContinuousOn σ (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (σ t : E → ℝ) ∧
          ‖ξ t‖ ≤ C₀ * M ∧ |β| * ‖ξ t‖ ≤ 1 / 2 ∧ ‖σ t‖ ≤ (2 * C₀) * M ∧
          (∀ x, σ t x = coleHopfInv β (ξ t x)) ∧ coleHopfBUC β (σ t) = ξ t) ∧
        (∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r ↦ σ r x)
          (a * Δ (σ t : E → ℝ) x + (c / 2) * ‖∇ (σ t : E → ℝ) x‖ ^ 2 -
            delayedHeatForcing a p N t x) t) ∧
        (∀ η, IsForcedColeHopfMild a β (delayedHeatForcing a p N) η T →
          EqOn η ξ (Icc 0 T)) := by
  obtain ⟨C₀, hC₀, M₀, hM₀, hex⟩ := exists_forcedColeHopf_mild_phase (E := E) β C hC
  refine ⟨C₀, hC₀, M₀, hM₀, ?_⟩
  intro a c T M p N ha hcancel hT hM hMM hdecay
  obtain ⟨ξ, σ, hξ, hσc, hσ0, hb, hu⟩ := hex a T M (delayedHeatForcing a p N)
    hT hM hMM (continuous_delayedHeatForcing a p N).continuousOn hdecay
  obtain ⟨hspace, htime⟩ := hξ.delayed_phase_classical ha hT hcancel
    (fun t ht ↦ (hb t ht).2.1) (fun t ht ↦ (hb t ht).2.2.2.1)
  exact ⟨ξ, σ, hξ, hσc, hσ0, fun t ht ↦ ⟨hspace t ht, hb t ht⟩, htime, hu⟩

end

end Planarwave
