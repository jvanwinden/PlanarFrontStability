/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontLinearizedMild
import all Planarwave.Analysis.DiffusionGenerator
import all Planarwave.Analysis.DiffusionSemigroup
import Planarwave.Analysis.SemigroupPerturbationGenerator
import Planarwave.Analysis.SemigroupPerturbationBound

/-!
# The real-frequency linearized front semigroup

The first bounded perturbation in Lemma 2.2 adds multiplication by `f'(φ)` to the principal
diffusion semigroup. Its full generator is the longitudinal pencil on precisely `ComplexBUC2`,
and its norm satisfies the frequency-uniform estimate (2.3).
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- The real-frequency longitudinal semigroup, constructed with the actual front coefficient. -/
def frontLinearizedC0Semigroup (q : ℝ) : C0Semigroup ℂ (BUC ℝ (ℂ^n)) :=
  (frontDiffusionC0Semigroup D h₁.positive c q).boundedPerturbation
    (frontReactionMultiplication f D c φ h₁ h₂)

/-- The global semigroup agrees with the previously constructed finite-horizon mild paths. -/
theorem frontLinearizedC0Semigroup_eq_mildPath (q : ℝ) {t T : NNReal} (ht : t ≤ T)
    (x : BUC ℝ (ℂ^n)) :
    frontLinearizedC0Semigroup f D c φ h₁ h₂ q t x =
      frontLinearizedMildPathOperator f D c φ h₁ h₂ q T x ⟨t, t.2, ht⟩ :=
  C0Semigroup.perturbedOperator_eq_path _ _ ht x

/-- Exact generator and full domain for the real-frequency longitudinal pencil. -/
theorem frontLinearizedC0Semigroup_hasGeneratorAt_iff (q : ℝ) (x y : BUC ℝ (ℂ^n)) :
    (frontLinearizedC0Semigroup f D c φ h₁ h₂ q).HasGeneratorAt x y ↔
      ∃ v : ComplexBUC2 (ℂ^n), ComplexBUC2.value (ℂ^n) v = x ∧
        frontLongitudinalPencil f D c φ h₁ h₂ (q : ℂ) v = y := by
  rw [frontLinearizedC0Semigroup, C0Semigroup.boundedPerturbation_hasGeneratorAt_iff,
    frontDiffusionC0Semigroup_hasGeneratorAt_iff D h₁.positive h₁.kernel]
  apply exists_congr
  intro v
  constructor
  · rintro ⟨hv, hy⟩
    refine ⟨hv, ?_⟩
    rw [frontLongitudinalPencil_eq_principal_add]
    change longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 v +
      frontReactionMultiplication f D c φ h₁ h₂ (ComplexBUC2.value (ℂ^n) v) = y
    rw [hv, hy, sub_add_cancel]
  · rintro ⟨hv, hy⟩
    refine ⟨hv, ?_⟩
    rw [frontLongitudinalPencil_eq_principal_add] at hy
    change longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 v +
      frontReactionMultiplication f D c φ h₁ h₂ (ComplexBUC2.value (ℂ^n) v) = y at hy
    rw [hv] at hy
    exact eq_sub_iff_add_eq.mpr hy

/-- Equation (2.3): the reaction perturbation costs a frequency-independent growth rate. -/
theorem exists_uniform_frontLinearized_bound :
    ∃ M > 0, ∃ μ > 0, ∃ C > 0, ∀ q : ℝ, 0 ≤ q → ∀ t : NNReal,
      ‖frontLinearizedC0Semigroup f D c φ h₁ h₂ q t‖ ≤
        M * Real.exp (C * t - μ * q * t) := by
  obtain ⟨M, hM, μ, hμ, hbound⟩ :=
    exists_uniform_frontDiffusion_bound D h₁.positive h₁.kernel
  let B := frontReactionMultiplication f D c φ h₁ h₂
  refine ⟨M, hM, μ, hμ, M * ‖B‖ + 1, by positivity, ?_⟩
  intro q hq t
  have h := (frontDiffusionC0Semigroup D h₁.positive c q).norm_boundedPerturbation_le B
    hM.le (hbound c q hq) t
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  nlinarith [t.2]

end

end Planarwave
