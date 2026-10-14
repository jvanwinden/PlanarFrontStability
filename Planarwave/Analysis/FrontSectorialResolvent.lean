/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAnalyticSemigroup
import all Planarwave.Analysis.FrontLaplaceResolvent
import Planarwave.Analysis.SectorialResolvent

/-!
# Uniform sectorial resolvent bounds for the longitudinal pencil

The analytic semigroups constructed for Section 2 give a common spectral wedge
on bounded sets of complex Fourier parameters. A uniform sectorial resolvent
estimate excludes high imaginary spectral parameters and bounds the spectrum
inside the corresponding sector.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- One sectorial resolvent estimate works for every pencil parameter in a
prescribed bounded set. All constants are chosen before the parameter. -/
theorem exists_uniform_frontPencil_sectorial_resolvent_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ a > 0, ∃ C > 0, ∃ Ω > 0, ∀ q : ℂ, ‖q‖ ≤ R → ∀ z : ℂ,
      Ω < z.re + a * |z.im| →
        (frontPencilClosedOperator f D c φ h₁ h₂ q).IsInResolvent z ∧
        ‖(frontPencilClosedOperator f D c φ h₁ h₂ q).ambientResolvent z‖ ≤
          C / (z.re + a * |z.im| - Ω) := by
  obtain ⟨η, hη, _, M, hM, ω, hω, hext⟩ :=
    exists_frontPencil_holomorphic_sector f D c φ h₁ h₂
  let a := η / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have haη : a < η := by dsimp [a]; linarith
  let M' := max M 1
  have hM' : 1 ≤ M' := le_max_right _ _
  let ω' := ω + M * R * ‖frontComplexifiedDiffusionBUC D‖
  have hω' : 0 < ω' := add_pos_of_pos_of_nonneg hω (by positivity)
  refine ⟨a, ha, (1 + a) * M', by positivity, ω' * (1 + a), by positivity, ?_⟩
  intro q hq z hz
  obtain ⟨G, hGa, hreal, _, hzero, hb⟩ := hext q
  let S := frontPencilC0Semigroup f D c φ h₁ h₂ q
  let A := frontPencilClosedOperator f D c φ h₁ h₂ q
  have hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y :=
    frontPencilC0Semigroup_hasGeneratorAt_iff f D c φ h₁ h₂ q
  have hbound : ∀ w ∈ complexTimeSector η, ‖G w‖ ≤ M' * Real.exp (ω' * ‖w‖) := by
    intro w hw
    apply (hb w hw).trans
    apply mul_le_mul (le_max_left M 1) _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
    dsimp only [ω']
    gcongr
  exact A.resolvent_bound_on_sector_complement S hgen ha haη hM' hω'.le
    hGa hreal hzero hbound z hz

/-- Uniform exclusion of spectral parameters outside a leftward wedge. -/
theorem exists_uniform_frontPencil_spectrum_sector_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ a > 0, ∃ Ω > 0, ∀ q : ℂ, ‖q‖ ≤ R → ∀ z : ℂ,
      z ∈ (frontPencilClosedOperator f D c φ h₁ h₂ q).spectrum →
        z.re + a * |z.im| ≤ Ω := by
  obtain ⟨a, ha, _, _, Ω, hΩ, hres⟩ :=
    exists_uniform_frontPencil_sectorial_resolvent_bound f D c φ h₁ h₂ hR
  refine ⟨a, ha, Ω, hΩ, ?_⟩
  intro q hq z hz
  by_contra! hlt
  exact hz (hres q hq z hlt).1

end

end Planarwave
