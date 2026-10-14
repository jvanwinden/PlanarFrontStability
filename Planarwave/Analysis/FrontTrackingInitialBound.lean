/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingSystem

/-!
# The initial nonlinear estimate for coupled tracking

At the initial time the delayed forcing, phase gradient, and phase Laplacian
vanish. Consequently the source is purely the quadratic Taylor remainder,
even for initial perturbations with no spatial derivatives. This is the
initial estimate used to start the nonlinear bootstrap in `lem:key`.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ}
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- The phase of a coupled tracking system vanishes through its first
quarter interval, without any smallness or nonlinear bootstrap assumption. -/
theorem FrontTrackingSystem.phase_initial_zero {T t : ℝ}
    (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T)
    (ht : t ∈ Icc 0 T) (hq : t ≤ 1 / 4) : X.σ t = 0 :=
  frontForcedPhase_initial_zero f D c φ ψ h₃ X.coleHopf_mild ht hq
    (X.coleHopf_eq t ht)

/-- The initial source is quadratic in the initial perturbation. There is
no source bootstrap hypothesis and no requirement on the initial jets. -/
theorem exists_frontTrackingSystem_initial_source_bound :
    ∃ A > 0, ∀ (T : ℝ) (X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T)
      (M : ℝ), 0 ≤ M → M ≤ 1 → ‖X.v₀‖ ≤ M →
        ‖X.N 0‖ ≤ A * M ^ 2 ∧ X.σ 0 = 0 := by
  obtain ⟨A, hA, hb⟩ := exists_frontInverseModulationNonlinearity_bound
    (m := d - 1) f D c φ ψ h₁ h₂ (R := 1) (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro T X M hM hM1 hv₀
  have ht : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, X.nonneg⟩
  have hq : (0 : ℝ) ≤ 1 / 4 := by norm_num
  obtain ⟨hs, hl, hg⟩ := X.initial_zero ht hq
  have hN : X.N 0 = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
      X.v₀ (X.v₁ 0) (X.v₂ 0) 0 0 0 := by
    rw [X.source_eq 0 ht, X.initial, hs, hl]
    change frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
      X.v₀ (X.v₁ 0) (X.v₂ 0) 0 0 (X.forcing 0) = _
    rw [hg]
  refine ⟨?_, X.phase_initial_zero f D c φ ψ h₁ h₂ h₃ hd ht hq⟩
  rw [hN]
  have hquad := hb X.v₀ (X.v₁ 0) (X.v₂ 0) 0 0 0 (hv₀.trans hM1)
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, mul_zero] at hquad
  exact hquad.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv₀ 2) hA.le)

end

end Planarwave
