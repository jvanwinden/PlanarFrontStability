/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Planarwave.Coordinates
import all Planarwave.Analysis.TwoEndedBUC
import all Planarwave.Analysis.ChallengeBridge

/-!
# Initial phase data for the viscous Hamilton--Jacobi equation

The nonlinear theorem in `Challenge.lean` defines the initial phase by integrating the pairing of
the adjoint profile with the initial perturbation along each longitudinal slice.  This file proves
integrability of the defining integrand, bounded uniform continuity of the phase, and its
supremum-norm bound and continuous dependence on the initial datum. These results provide
admissible initial data for the subsequent viscous Hamilton--Jacobi construction.
-/

open Filter Function MeasureTheory Set
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n)

/-- The integrand defining the initial phase is integrable on every transverse slice. -/
theorem integrable_initial_phase_integrand
    (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) (y : ℝ^(d - 1)) :
    Integrable (fun z : ℝ => ⟪ψ z, φ z - u₀ (full y z)⟫_ℝ) := by
  obtain ⟨φ₁, φ₂, hleft, hright⟩ := h₂.endpoints
  obtain ⟨Cφ, hCφ⟩ :=
    (isBounded_range_of_tendsto_atBot_atTop h₂.smooth.continuous
      hleft hright).exists_norm_le
  rcases hu₀ with ⟨hu₀cont, ⟨C₀, hC₀⟩⟩
  let M : ℝ := max Cφ 0 + max C₀ 0
  have hu₀continuous : Continuous u₀ :=
    (uniformContinuousOn_univ.mp hu₀cont).continuous
  have hfull : Continuous (fun z : ℝ => full y z) := by
    have hpair : Continuous (fun z : ℝ => (y, z)) := by fun_prop
    change Continuous
      ((fun p : ℝ^(d - 1) × ℝ => full p.1 p.2) ∘ fun z : ℝ => (y, z))
    exact continuous_full.comp hpair
  have hperturbation_continuous :
      Continuous (fun z : ℝ => φ z - u₀ (full y z)) :=
    h₂.smooth.continuous.sub (hu₀continuous.comp hfull)
  have hperturbation_bound :
      ∀ z : ℝ, ‖φ z - u₀ (full y z)‖ ≤ M := by
    intro z
    dsimp [M]
    calc
      ‖φ z - u₀ (full y z)‖ ≤ ‖φ z‖ + ‖u₀ (full y z)‖ := norm_sub_le _ _
      _ ≤ max Cφ 0 + max C₀ 0 := by
        gcongr
        · exact le_max_of_le_left (hCφ (φ z) ⟨z, rfl⟩)
        · exact le_max_of_le_left (hC₀ (full y z) (Set.mem_univ _))
  have hmajorant : Integrable (fun z : ℝ => M * ‖ψ z‖) := by
    exact (h₃.integrable.norm).const_mul M
  refine hmajorant.mono' ?_ ?_
  · exact h₃.integrable.aestronglyMeasurable.inner
      hperturbation_continuous.aestronglyMeasurable
  · filter_upwards [] with z
    calc
      ‖⟪ψ z, φ z - u₀ (full y z)⟫_ℝ‖ ≤
          ‖ψ z‖ * ‖φ z - u₀ (full y z)‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ z‖ * M :=
        mul_le_mul_of_nonneg_left (hperturbation_bound z) (norm_nonneg _)
      _ = M * ‖ψ z‖ := by ring

/-- The initial phase integrand has the sharp pointwise bound supplied by the initial closeness
condition.  Consequently its integral is `O(E₀)`, uniformly in the transverse slice. -/
theorem norm_initial_phase_le
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) (ε : ℝ)
    (hclose : IsCloseToFront φ u₀ ε) (y : ℝ^(d - 1)) :
    ‖∫ z : ℝ, ⟪ψ z, φ z - u₀ (full y z)⟫_ℝ‖ ≤
      ε * ∫ z : ℝ, ‖ψ z‖ := by
  have hintegrable := integrable_initial_phase_integrand f D c φ ψ h₂ h₃ hu₀ y
  have hmajorant : Integrable (fun z : ℝ => ε * ‖ψ z‖) :=
    (h₃.integrable.norm).const_mul ε
  have hclose_full :
      ∀ z : ℝ, ‖φ z - u₀ (full y z)‖ ≤ ε := by
    intro z
    have hz := (isCloseToFront_iff_full_coordinates hd φ u₀ ε).mp hclose y z
    simpa only [norm_sub_rev] using hz
  calc
    ‖∫ z : ℝ, ⟪ψ z, φ z - u₀ (full y z)⟫_ℝ‖ ≤
        ∫ z : ℝ, ‖⟪ψ z, φ z - u₀ (full y z)⟫_ℝ‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ, ε * ‖ψ z‖ := by
      apply integral_mono hintegrable.norm hmajorant
      intro z
      calc
        ‖⟪ψ z, φ z - u₀ (full y z)⟫_ℝ‖ ≤
            ‖ψ z‖ * ‖φ z - u₀ (full y z)‖ := norm_inner_le_norm _ _
        _ ≤ ‖ψ z‖ * ε :=
          mul_le_mul_of_nonneg_left (hclose_full z) (norm_nonneg _)
        _ = ε * ‖ψ z‖ := by ring
    _ = ε * ∫ z : ℝ, ‖ψ z‖ := integral_const_mul ε _

/-! ## The transverse initial phase -/

/-- The initial phase prescribed in the challenge theorem. -/
def initialPhase (u₀ : ℝ^d → ℝ^n) (y : ℝ^(d - 1)) : ℝ :=
  ∫ z : ℝ, ⟪ψ z, φ z - u₀ (full y z)⟫_ℝ

/-- Differences of initial phases are controlled by differences of the initial data on the
corresponding slices; the front profile cancels. -/
theorem norm_initialPhase_sub_le
    (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ v₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) (hv₀ : IsBUC v₀)
    (y y' : ℝ^(d - 1)) (a : ℝ)
    (ha : ∀ z : ℝ, ‖u₀ (full y z) - v₀ (full y' z)‖ ≤ a) :
    ‖initialPhase φ ψ u₀ y - initialPhase φ ψ v₀ y'‖ ≤
      a * ∫ z : ℝ, ‖ψ z‖ := by
  rw [initialPhase, initialPhase, ← integral_sub
    (integrable_initial_phase_integrand f D c φ ψ h₂ h₃ hu₀ y)
    (integrable_initial_phase_integrand f D c φ ψ h₂ h₃ hv₀ y')]
  calc
    ‖∫ z : ℝ, ⟪ψ z, φ z - u₀ (full y z)⟫_ℝ -
        ⟪ψ z, φ z - v₀ (full y' z)⟫_ℝ‖ ≤ ∫ z : ℝ, a * ‖ψ z‖ := by
      apply norm_integral_le_of_norm_le (h₃.integrable.norm.const_mul a)
      filter_upwards [] with z
      rw [← inner_sub_right, sub_sub_sub_cancel_left]
      calc
        ‖⟪ψ z, v₀ (full y' z) - u₀ (full y z)⟫_ℝ‖ ≤
            ‖ψ z‖ * ‖v₀ (full y' z) - u₀ (full y z)‖ := norm_inner_le_norm _ _
        _ ≤ ‖ψ z‖ * a := by
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (ha z) (norm_nonneg _)
        _ = a * ‖ψ z‖ := mul_comm _ _
    _ = a * ∫ z : ℝ, ‖ψ z‖ := integral_const_mul a _

/-- Uniform continuity of the full initial datum passes to its transverse initial phase. -/
theorem uniformContinuous_initialPhase
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) :
    UniformContinuous (initialPhase φ ψ u₀) := by
  have hcoord : UniformContinuous
      (fun p : ℝ^(d - 1) × ℝ => u₀ (full p.1 p.2)) :=
    (uniformContinuousOn_univ.mp hu₀.1).comp
      (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous
  let W : ℝ := ∫ z : ℝ, ‖ψ z‖
  have hW : 0 ≤ W := integral_nonneg fun z => norm_nonneg (ψ z)
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hden : 0 < W + 1 := by positivity
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hcoord
    (ε / (W + 1)) (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro y y' hyy'
  have hslice : ∀ z : ℝ,
      ‖u₀ (full y z) - u₀ (full y' z)‖ ≤ ε / (W + 1) := by
    intro z
    have hp : dist (y, z) (y', z) < δ := by simpa using hyy'
    simpa only [dist_eq_norm] using (hmod hp).le
  rw [dist_eq_norm]
  calc
    ‖initialPhase φ ψ u₀ y - initialPhase φ ψ u₀ y'‖ ≤ ε / (W + 1) * W :=
      norm_initialPhase_sub_le f D c φ ψ h₂ h₃ hu₀ hu₀ y y' _ hslice
    _ < ε := by
      have hpos : 0 < ε / (W + 1) := div_pos hε hden
      have heq : ε / (W + 1) * (W + 1) = ε := div_mul_cancel₀ ε hden.ne'
      nlinarith

/-- The phase prescribed by the challenge is admissible bounded uniformly continuous initial
data for the viscous Hamilton--Jacobi equation. -/
theorem isBUC_initialPhase
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) : IsBUC (initialPhase φ ψ u₀) := by
  obtain ⟨C, hC⟩ := hu₀.2
  refine ⟨(uniformContinuous_initialPhase f D c φ ψ hd h₂ h₃ hu₀).uniformContinuousOn,
    2 * C * (∫ z : ℝ, ‖ψ z‖) + ‖initialPhase φ ψ u₀ 0‖, ?_⟩
  intro y _
  have hslice : ∀ z : ℝ, ‖u₀ (full y z) - u₀ (full 0 z)‖ ≤ 2 * C := by
    intro z
    calc
      ‖u₀ (full y z) - u₀ (full 0 z)‖ ≤
          ‖u₀ (full y z)‖ + ‖u₀ (full 0 z)‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC _ (mem_univ _)) (hC _ (mem_univ _))
      _ = 2 * C := by ring
  have hdiff := norm_initialPhase_sub_le f D c φ ψ h₂ h₃ hu₀ hu₀ y 0 (2 * C) hslice
  exact (norm_le_norm_sub_add _ _).trans (add_le_add hdiff le_rfl)

/-- The challenge's initial phase as an element of the transverse BUC Banach space. -/
def initialPhaseBUC
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) : BUC (ℝ^(d - 1)) ℝ :=
  BUC.ofIsBUC (isBUC_initialPhase f D c φ ψ hd h₂ h₃ hu₀)

@[simp]
theorem initialPhaseBUC_apply
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) (y : ℝ^(d - 1)) :
    initialPhaseBUC f D c φ ψ hd h₂ h₃ hu₀ y =
      ∫ z : ℝ, ⟪ψ z, φ z - u₀ (full y z)⟫_ℝ := rfl

/-- Small initial perturbations give small phase data in the BUC norm. -/
theorem norm_initialPhaseBUC_le
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) {ε : ℝ}
    (hclose : IsCloseToFront φ u₀ ε) :
    ‖initialPhaseBUC f D c φ ψ hd h₂ h₃ hu₀‖ ≤ ε * ∫ z : ℝ, ‖ψ z‖ := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hclose 0)
  apply (BUC.norm_le (mul_nonneg hε (integral_nonneg fun z => norm_nonneg (ψ z)))).2
  intro y
  exact norm_initial_phase_le f D c φ ψ hd h₂ h₃ hu₀ ε hclose y

/-- The initial phase map is Lipschitz in the supremum norm, with constant bounded by the
adjoint profile's `L¹` norm. -/
theorem norm_initialPhaseBUC_sub_le
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    {u₀ v₀ : ℝ^d → ℝ^n} (hu₀ : IsBUC u₀) (hv₀ : IsBUC v₀) :
    ‖initialPhaseBUC f D c φ ψ hd h₂ h₃ hu₀ -
        initialPhaseBUC f D c φ ψ hd h₂ h₃ hv₀‖ ≤
      ‖BUC.ofIsBUC hu₀ - BUC.ofIsBUC hv₀‖ * ∫ z : ℝ, ‖ψ z‖ := by
  apply (BUC.norm_le (mul_nonneg (norm_nonneg _)
    (integral_nonneg fun z => norm_nonneg (ψ z)))).2
  intro y
  exact norm_initialPhase_sub_le f D c φ ψ h₂ h₃ hu₀ hv₀ y y _
    (fun z => (BUC.ofIsBUC hu₀ - BUC.ofIsBUC hv₀).norm_apply_le (full y z))

end

end Planarwave
