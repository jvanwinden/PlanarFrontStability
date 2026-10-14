/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingSystem
import all Planarwave.Analysis.FrontPhysicalNonlinearSource

/-!
# Constructing the coupled tracking system before the first forcing pulse

On the initial quarter interval the delayed forcing vanishes independently
of its input source. Thus zero phase and Cole--Hopf paths solve the phase
equation, and the actual physical perturbation supplies its own continuous
nonlinear source. This gives the initial causal construction for the paper's
tracking scheme, without a source bootstrap or initial spatial derivatives.
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

/-- The physical mild solution admits a self-consistent coupled tracking
system up to time `1/4`. Its phase is identically zero. -/
theorem exists_frontTrackingInitialSystem {T : ℝ} (hT : 0 ≤ T) (hquarter : T ≤ 1 / 4)
    (u : ℝ → BUC (ℝ^d) (ℝ^n)) (hu : ContinuousOn u (Icc 0 T))
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (hv₀ : frontInverseModulatedPerturbation f D c φ h₂ hd (u 0) (c * 0) 0 = v₀) :
    ∃ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T,
      X.u = u ∧ X.v₀ = v₀ ∧ X.σ = (fun _ ↦ 0) ∧ X.ξ = (fun _ ↦ 0) := by
  obtain ⟨v₁, v₂, N, _, _, hNc, hd₁, hd₂, hNeq⟩ :=
    exists_front_physical_nonlinear_source f D c φ ψ h₁ h₂ h₃ hd
      (δ := 1) hT (by norm_num) u hu hm (fun _ ↦ 0) continuousOn_const
      (BUCSpatialRegularOn.zero _ 2) (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0)
      continuousOn_const continuousOn_const continuousOn_const (by simp)
  have hg : ∀ t ∈ Icc 0 T, frontDelayedForcing f D c φ ψ h₃ v₀ N t = 0 := by
    intro t ht
    exact frontDelayedForcing_initial_zero f D c φ ψ h₃ v₀ N (ht.2.trans hquarter)
  let X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T := {
    nonneg := hT
    u := u
    ξ := fun _ ↦ 0
    σ := fun _ ↦ 0
    s := fun _ ↦ 0
    l := fun _ ↦ 0
    v₀ := v₀
    N := N
    v₁ := v₁
    v₂ := v₂
    physical_continuous := hu
    physical_mild := hm
    phase_regular := BUCSpatialRegularOn.zero _ 2
    gradient_continuous := continuousOn_const
    laplacian_continuous := continuousOn_const
    source_continuous := hNc
    initial := hv₀
    coleHopf_mild := (isForcedColeHopfMild_zero (d_perp D φ ψ)
      (c / (2 * d_perp D φ ψ)) T).congr_forcing (fun t ht ↦ (hg t ht).symm)
    coleHopf_eq := by
      intro t ht
      ext y
      simp only [coleHopfBUC_apply, BUC.zero_apply, coleHopf_zero_apply]
    gradient_eq := by
      intro t ht y
      change (0 : ℝ^(d - 1)) = ∇ (fun _ : ℝ^(d - 1) ↦ (0 : ℝ)) y
      exact (gradient_fun_const y 0).symm
    laplacian_eq := by
      intro t ht y
      change (0 : ℝ) = Δ (fun _ : ℝ^(d - 1) ↦ (0 : ℝ)) y
      simp
    phase_pde := by
      intro t ht y
      rw [hg t ⟨ht.1.le, ht.2.le⟩]
      simpa using (hasDerivAt_const t (0 : ℝ))
    first_derivative := hd₁
    second_derivative := hd₂
    source_eq := by
      intro t ht
      rw [hg t ht]
      exact hNeq t }
  exact ⟨X, rfl, rfl, rfl, rfl⟩

end

end Planarwave
