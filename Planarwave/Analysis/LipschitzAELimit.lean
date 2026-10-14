/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

/-!
# Lipschitz representatives of almost-everywhere limits

A common Lipschitz constant upgrades almost-everywhere convergence to
everywhere convergence to a Lipschitz representative. Full-measure subsets of
the real line are dense; the Cauchy criterion then extends from this dense
subset to each point. No pointwise regularity of the original representative
is required.
-/

open MeasureTheory Filter
open scoped Topology NNReal

namespace Planarwave

variable {F : Type*} [MetricSpace F] [CompleteSpace F]

/-- Almost-everywhere convergence of uniformly Lipschitz functions determines
a Lipschitz representative and upgrades the convergence to every point. -/
theorem exists_lipschitz_representative_of_ae_tendsto
    {u : ℕ → ℝ → F} {ψ : ℝ → F} {K : ℝ≥0}
    (hu : ∀ j, LipschitzWith K (u j))
    (hlim : ∀ᵐ x, Tendsto (fun j ↦ u j x) atTop (𝓝 (ψ x))) :
    ∃ χ : ℝ → F, LipschitzWith K χ ∧ ψ =ᵐ[volume] χ ∧
      ∀ x, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)) := by
  have hdense := volume.dense_of_ae hlim
  have hcauchy (x : ℝ) : CauchySeq (fun j ↦ u j x) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨y, hyx, hy⟩ := Metric.dense_iff.mp hdense x
      (ε / (6 * ((K : ℝ) + 1))) (by positivity)
    have hxy : (K : ℝ) * dist x y < ε / 6 := by
      have hdist : dist x y < ε / (6 * ((K : ℝ) + 1)) := by
        simpa only [Metric.mem_ball, dist_comm] using hyx
      have hpos : 0 < 6 * ((K : ℝ) + 1) := by positivity
      have hlt := (lt_div_iff₀ hpos).mp hdist
      have hnonneg := dist_nonneg (x := x) (y := y)
      nlinarith
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hy.cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun j hj ↦ ?_⟩
    have h₁ := (hu j).dist_le_mul x y
    have h₂ := (hu N).dist_le_mul y x
    have h₃ := dist_triangle (u j x) (u j y) (u N x)
    have h₄ := dist_triangle (u j y) (u N y) (u N x)
    rw [dist_comm y x] at h₂
    have := hN j hj
    linarith
  choose χ hχ using fun x ↦ cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨χ, LipschitzWith.of_dist_le_mul (fun x y ↦ ?_), ?_, hχ⟩
  · exact le_of_tendsto ((hχ x).dist (hχ y)) (Filter.Eventually.of_forall fun j ↦ (hu j).dist_le_mul x y)
  · filter_upwards [hlim] with x hx
    exact tendsto_nhds_unique hx (hχ x)

end Planarwave
