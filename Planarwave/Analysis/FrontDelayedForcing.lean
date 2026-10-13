/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontProjectedNonlinearity
import Planarwave.Analysis.DelayedHeatForcingSmoothing
import Planarwave.Analysis.DelayedHeatForcingRegularity

/-!
# Delayed forcing for the actual front

Specialize `eq:defgnew` to the original transverse diffusivity and adjoint
projection. The source path is later chosen as the inverse-modulation
nonlinearity; the final bound below makes this choice explicitly and uses
Lemma 4.2, with no derivative norms of the perturbation in the conclusion.
This constructs forcing from a supplied source, not yet the coupled solution.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The front forcing, with initial perturbation `v₀` and nonlinear source `N`. -/
def frontDelayedForcing (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) :
    ℝ → BUC (ℝ^m) ℝ :=
  delayedHeatForcing (d_perp D φ ψ) (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))

theorem contDiff_frontDelayedForcing (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ^m ↦ frontDelayedForcing f D c φ ψ h₃ v₀ N q.1 q.2) :=
  contDiff_delayedHeatForcing h₃.transverse_low_wavenumber _ _

theorem continuous_frontDelayedForcing (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) :
    Continuous (frontDelayedForcing f D c φ ψ h₃ v₀ N) :=
  continuous_delayedHeatForcing _ _ _

theorem frontDelayedForcing_causal (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    {N M : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)} (k : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (h : EqOn N M (Icc (0 : ℝ) (k : ℝ))) :
    frontDelayedForcing f D c φ ψ h₃ v₀ N ((k : ℝ) + τ) =
      frontDelayedForcing f D c φ ψ h₃ v₀ M ((k : ℝ) + τ) :=
  delayedHeatForcing_causal _ _ k hτ (fun _ hr ↦ congrArg _ (h hr))

theorem norm_frontDelayedForcing_initial_le (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) {t : ℝ} (ht : t ≤ 1) :
    ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖ ≤
      trackingCutoff t * (∫ z, ‖ψ z‖) * ‖v₀‖ := by
  calc
    _ ≤ trackingCutoff t * ‖longitudinalPairing ψ h₃.integrable v₀‖ :=
      norm_delayedHeatForcing_initial_le _ _ _ ht
    _ ≤ trackingCutoff t * ((∫ z, ‖ψ z‖) * ‖v₀‖) :=
      mul_le_mul_of_nonneg_left (norm_longitudinalPairing_le ψ h₃.integrable v₀)
        (trackingCutoff_nonneg t)
    _ = _ := (mul_assoc _ _ _).symm

/-- The direct block bound used at the start of the nonlinear bootstrap. -/
theorem norm_frontDelayedForcing_block_le (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (k : ℕ) {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ∀ r ∈ Icc (k : ℝ) ((k : ℝ) + 1), ‖N r‖ ≤ M) :
    ‖frontDelayedForcing f D c φ ψ h₃ v₀ N ((k : ℝ) + 1 + τ)‖ ≤
      trackingCutoff τ * (∫ z, ‖ψ z‖) * M := by
  apply (norm_delayedHeatForcing_block_le _ _ _ k hτ (fun r hr ↦
    (norm_longitudinalPairing_le ψ h₃.integrable (N r)).trans
      (mul_le_mul_of_nonneg_left (hN r hr) (integral_nonneg fun z ↦ norm_nonneg (ψ z))))).trans_eq
  exact (mul_assoc _ _ _).symm

/-- The derivative-free block estimate for the actual nonlinear source.
The constant is chosen before all paths and all time blocks. -/
theorem exists_frontDelayedForcing_nonlinear_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ v₀ : BUC (ℝ^m × ℝ) (ℝ^n),
      ∀ N v : ℝ → BUC (ℝ^m × ℝ) (ℝ^n),
      ∀ v₁ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ v₂ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ σ : ℝ → ℝ^m → ℝ, ∀ s : ℝ → BUC (ℝ^m) (ℝ^m),
      ∀ s₁ : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m), ∀ l g : ℝ → BUC (ℝ^m) ℝ,
      ∀ k : ℕ, ∀ τ A : ℝ, τ ∈ Icc (0 : ℝ) 1 →
      ContinuousOn N (Icc (k : ℝ) ((k : ℝ) + 1)) →
      (∀ r ∈ Icc (k : ℝ) ((k : ℝ) + 1),
        N r = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ (v r) (v₁ r) (v₂ r) (s r) (l r) (g r) ∧
        (∀ x, HasFDerivAt (v r) (v₁ r x) x) ∧ (∀ x, HasFDerivAt (v₁ r) (v₂ r x) x) ∧
        (∀ y, s r y = ∇ (σ r) y) ∧ (∀ y, HasFDerivAt (s r) (s₁ r y) y) ∧
        (∀ y, l r y = Δ (σ r) y) ∧ ‖v r‖ ≤ R ∧
        ‖v r‖ * (‖v r‖ + ‖l r‖ + ‖s r‖ + ‖s r‖ ^ 2 + ‖g r‖) ≤ A) →
      ‖frontDelayedForcing f D c φ ψ h₃ v₀ N ((k : ℝ) + 1 + τ)‖ ≤
        trackingCutoff τ * (C * A) := by
  obtain ⟨C, hC, hb⟩ := exists_frontSmoothedNonlinearity_bound (m := m) f D c φ ψ h₁ h₂ h₃ hR
  refine ⟨C, hC, fun v₀ N v v₁ v₂ σ s s₁ l g k τ A hτ hN hdata ↦ ?_⟩
  apply norm_delayedHeatForcing_block_smoothed_le h₃.transverse_low_wavenumber.le _ _ k hτ
    ((longitudinalPairing ψ h₃.integrable).continuous.comp_continuousOn hN)
  intro r hr
  obtain ⟨hNr, hv₁, hv₂, hs, hs₁, hl, hv, hA⟩ := hdata r hr
  dsimp only [Function.comp_def]
  rw [hNr]
  calc
    _ ≤ C * ‖v r‖ * (‖v r‖ + ‖l r‖ + ‖s r‖ + ‖s r‖ ^ 2 + ‖g r‖) :=
      hb (v r) (v₁ r) (v₂ r) (σ r) (s r) (s₁ r) (l r) (g r) hv₁ hv₂ hs hs₁ hl hv
    _ ≤ C * A := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hA hC.le

end

end Planarwave
