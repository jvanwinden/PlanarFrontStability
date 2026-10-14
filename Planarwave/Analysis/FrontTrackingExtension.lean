/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingPhaseExtension
import all Planarwave.Analysis.FrontTrackingSourceCongruence
import all Planarwave.Analysis.FrontPhysicalNonlinearSource

/-!
# One causal extension step for the coupled tracking equations

This is the extension step in Proposition `tracking`. First extend the
forcing using only the old source, and solve the forced phase equation.
Construct the new physical perturbation and its genuine nonlinear source.
Equality with the old source on the preceding slab then shows that the new
source generates exactly the forcing used to construct it.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- Extend the coupled tracking system to the next unit block. Only the
old source is assumed to satisfy the bootstrap estimate; no information
about the future nonlinear source is supplied. -/
theorem exists_frontTrackingSystem_extension :
    ∃ ε > 0, ∀ (k : ℕ) (T M : ℝ)
      (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd (k : ℝ)),
      (k : ℝ) ≤ T → T ≤ (k : ℝ) + 1 → 0 ≤ M → M ≤ ε → ‖X.v₀‖ ≤ M →
      (∀ t ∈ Icc 0 (k : ℝ), ‖X.N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ContinuousOn X.u (Icc 0 T) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T X.u →
      ∃ Y : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T,
        Y.u = X.u ∧ Y.v₀ = X.v₀ ∧ EqOn Y.σ X.σ (Icc 0 (k : ℝ)) ∧
        EqOn Y.N X.N (Icc 0 (k : ℝ)) := by
  obtain ⟨ε, hε, hphase⟩ := exists_frontTrackingPhaseExtension f D c φ ψ h₁ h₂ h₃ hd
  refine ⟨ε, hε, ?_⟩
  intro k T M X hkT hTk hM hMε hv₀ hN hu hm
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hT : 0 ≤ T := hk.trans hkT
  obtain ⟨ξ, σ, s, L, hξ, hreg, hsc, hLc, _, hfields, hPDE, _, hσeq, _, _⟩ :=
    hphase k T M X hkT hTk hM hMε hv₀ hN
  have hzero : ∀ t ∈ Icc 0 T, t < (1 : ℝ) / 4 →
      s t = 0 ∧ L t = 0 ∧ frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N t = 0 := by
    intro t ht hq
    exact frontTrackingCoefficients_initial_zero f D c φ ψ h₃ hξ ht hq.le
      (hfields t ht).2.2 (s t) (L t) (hfields t ht).1 (hfields t ht).2.1
  obtain ⟨v₁, v₂, N, _, _, hNc, hd₁, hd₂, hNeq⟩ :=
    exists_front_physical_nonlinear_source f D c φ ψ h₁ h₂ h₃ hd hT
      (by norm_num : (0 : ℝ) < 1 / 4) X.u hu hm σ (hreg 2).2.continuous
      ((hreg 2).2.mono Ioc_subset_Icc_self) s L
      (frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N)
      (hsc.mono Ioc_subset_Icc_self) (hLc.mono Ioc_subset_Icc_self)
      (continuous_frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N).continuousOn hzero
  have hNpast : EqOn N X.N (Icc 0 (k : ℝ)) := by
    intro t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hkT⟩
    rw [hNeq t]
    exact (X.source_eq_of_physical_fields_eq ht rfl (hσeq ht).symm rfl
      (fun hp ↦ hd₁ t ⟨hp, htT.2⟩) (fun hp ↦ hd₂ t ⟨hp, htT.2⟩)
      (hfields t htT).1 (hfields t htT).2.1).symm
  have hforcing : EqOn (frontDelayedForcing f D c φ ψ h₃ X.v₀ N)
      (frontDelayedForcing f D c φ ψ h₃ X.v₀ X.N) (Icc 0 T) := by
    intro t ht
    exact frontDelayedForcing_eqOn_of_past f D c φ ψ h₃ X.v₀ k hNpast (ht.2.trans hTk)
  let Y : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T := {
    nonneg := hT
    u := X.u
    ξ := ξ
    σ := σ
    s := s
    l := L
    v₀ := X.v₀
    N := N
    v₁ := v₁
    v₂ := v₂
    physical_continuous := hu
    physical_mild := hm
    phase_regular := (hreg 2).2
    gradient_continuous := hsc
    laplacian_continuous := hLc
    source_continuous := hNc
    initial := by simpa only [hσeq ⟨le_rfl, hk⟩] using X.initial
    coleHopf_mild := hξ.congr_forcing hforcing.symm
    coleHopf_eq := fun t ht ↦ (hfields t ht).2.2
    gradient_eq := fun t ht ↦ (hfields t ht).1
    laplacian_eq := fun t ht ↦ (hfields t ht).2.1
    phase_pde := by
      intro t ht y
      rw [hforcing ⟨ht.1.le, ht.2.le⟩]
      exact hPDE t ht y
    first_derivative := hd₁
    second_derivative := hd₂
    source_eq := by
      intro t ht
      rw [hforcing ht]
      exact hNeq t }
  exact ⟨Y, rfl, rfl, hσeq, hNpast⟩

end

end Planarwave
