/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/

module

public import Planarwave.Analysis.BUC
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public section

/-!
# Bounded uniformly continuous functions with two end states

A continuous function on the real line that converges at both ends is uniformly continuous and
has bounded range.  The two limits need not agree.  This elementary bridge is used for traveling
front profiles and for coefficients obtained by composing continuous maps with such profiles.
-/

open Bornology Filter Function Set Topology
open scoped ContDiff

namespace Planarwave

section UniformContinuity

variable {E : Type*} [PseudoMetricSpace E]

/-- A continuous function on `ℝ` with limits at both ends is uniformly continuous. -/
theorem uniformContinuous_of_tendsto_atBot_atTop
    {g : ℝ → E} {gNeg gPos : E} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos)) :
    UniformContinuous g := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hεtwo : 0 < ε / 2 := half_pos hε
  have hNegEventually : ∀ᶠ z in atBot, dist (g z) gNeg < ε / 2 :=
    hNeg (Metric.ball_mem_nhds gNeg hεtwo)
  have hPosEventually : ∀ᶠ z in atTop, dist (g z) gPos < ε / 2 :=
    hPos (Metric.ball_mem_nhds gPos hεtwo)
  obtain ⟨a, ha⟩ := mem_atBot_sets.mp hNegEventually
  obtain ⟨b, hb⟩ := mem_atTop_sets.mp hPosEventually
  let A := min a b
  let B := max a b
  have hAB : A ≤ B := min_le_max
  have hNegTail : ∀ z ≤ A, dist (g z) gNeg < ε / 2 := by
    intro z hz
    exact ha z (hz.trans (by simp [A]))
  have hPosTail : ∀ z, B ≤ z → dist (g z) gPos < ε / 2 := by
    intro z hz
    have hbB : b ≤ B := by simp [B]
    exact hb z (hbB.trans hz)
  have hcore : UniformContinuousOn g (Icc (A - 1) (B + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ₀, hδ₀, hδ₀mod⟩ := Metric.uniformContinuousOn_iff.mp hcore ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, ?_⟩
  intro x y hxy
  have hxy₀ : dist x y < δ₀ := hxy.trans_le (min_le_left _ _)
  have hxyOne : |x - y| < 1 := by
    rw [← Real.dist_eq]
    exact hxy.trans_le (min_le_right _ _)
  have hclose := (abs_lt.mp hxyOne)
  by_cases hx : x ∈ Icc (A - 1) (B + 1)
  · by_cases hy : y ∈ Icc (A - 1) (B + 1)
    · exact hδ₀mod x hx y hy hxy₀
    · simp only [mem_Icc, not_and_or] at hy
      rcases hy with hy | hy
      · have hxtail : x ≤ A := by linarith [hx.1]
        have hytail : y ≤ A := by linarith
        calc
          dist (g x) (g y) ≤ dist (g x) gNeg + dist gNeg (g y) := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := add_lt_add (hNegTail x hxtail)
            (by simpa [dist_comm] using hNegTail y hytail)
          _ = ε := by ring
      · have hxtail : B ≤ x := by linarith [hx.2]
        have hytail : B ≤ y := by linarith
        calc
          dist (g x) (g y) ≤ dist (g x) gPos + dist gPos (g y) := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := add_lt_add (hPosTail x hxtail)
            (by simpa [dist_comm] using hPosTail y hytail)
          _ = ε := by ring
  · simp only [mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · have hxtail : x ≤ A := by linarith
      have hytail : y ≤ A := by linarith
      calc
        dist (g x) (g y) ≤ dist (g x) gNeg + dist gNeg (g y) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (hNegTail x hxtail)
          (by simpa [dist_comm] using hNegTail y hytail)
        _ = ε := by ring
    · have hxtail : B ≤ x := by linarith
      have hytail : B ≤ y := by linarith
      calc
        dist (g x) (g y) ≤ dist (g x) gPos + dist gPos (g y) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (hPosTail x hxtail)
          (by simpa [dist_comm] using hPosTail y hytail)
        _ = ε := by ring

end UniformContinuity

section BoundedRange

variable {E : Type*} [PseudoMetricSpace E]

/-- A continuous function on `ℝ` with limits at both ends has bounded range. -/
theorem isBounded_range_of_tendsto_atBot_atTop
    {g : ℝ → E} {gNeg gPos : E} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos)) :
    IsBounded (range g) := by
  have hNegEventually : ∀ᶠ z in atBot, g z ∈ Metric.ball gNeg 1 :=
    hNeg (Metric.ball_mem_nhds gNeg one_pos)
  have hPosEventually : ∀ᶠ z in atTop, g z ∈ Metric.ball gPos 1 :=
    hPos (Metric.ball_mem_nhds gPos one_pos)
  obtain ⟨a, ha⟩ := mem_atBot_sets.mp hNegEventually
  obtain ⟨b, hb⟩ := mem_atTop_sets.mp hPosEventually
  let A := min a b
  let B := max a b
  have hNegTail : ∀ z ≤ A, g z ∈ Metric.ball gNeg 1 := by
    intro z hz
    exact ha z (hz.trans (by simp [A]))
  have hPosTail : ∀ z, B ≤ z → g z ∈ Metric.ball gPos 1 := by
    intro z hz
    have hbB : b ≤ B := by simp [B]
    exact hb z (hbB.trans hz)
  have hmiddle : IsBounded (g '' Icc A B) :=
    (isCompact_Icc.image_of_continuousOn hg.continuousOn).isBounded
  apply ((Metric.isBounded_ball.union hmiddle).union Metric.isBounded_ball).subset
  rintro _ ⟨x, rfl⟩
  by_cases hxA : x ≤ A
  · exact Or.inl (Or.inl (hNegTail x hxA))
  by_cases hxB : B ≤ x
  · exact Or.inr (hPosTail x hxB)
  · apply Or.inl
    apply Or.inr
    exact ⟨x, ⟨le_of_not_ge hxA, le_of_not_ge hxB⟩, rfl⟩

/-- In a proper metric space, the closure of the range of a two-ended continuous function is
compact.  Finite-dimensional normed spaces are the principal application. -/
theorem isCompact_closure_range_of_tendsto_atBot_atTop
    [ProperSpace E] {g : ℝ → E} {gNeg gPos : E} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos)) :
    IsCompact (closure (range g)) :=
  (isBounded_range_of_tendsto_atBot_atTop hg hNeg hPos).isCompact_closure

end BoundedRange

section Bundling

variable {E : Type*} [NormedAddCommGroup E]

/-- Canonically bundle a continuous function with two end states as a bounded uniformly
continuous function. -/
@[expose]
def BUC.ofTwoEnded {g : ℝ → E} {gNeg gPos : E} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos)) : BUC ℝ E where
  toBCF :=
    { toFun := g
      continuous_toFun := hg
      map_bounded' := Metric.isBounded_range_iff.mp
        (isBounded_range_of_tendsto_atBot_atTop hg hNeg hPos) }
  uniformContinuous' := uniformContinuous_of_tendsto_atBot_atTop hg hNeg hPos

@[simp]
theorem BUC.ofTwoEnded_apply {g : ℝ → E} {gNeg gPos : E} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos)) (z : ℝ) :
    BUC.ofTwoEnded hg hNeg hPos z = g z := rfl

end Bundling

section Composition

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- It suffices for the postcomposed map to be continuous on the compact closure of the range.
This form is useful when the coefficient map is only constructed on a neighborhood of the front
profile. -/
theorem uniformContinuous_comp_of_continuousOn_closure_range
    [ProperSpace E] {g : ℝ → E} {gNeg gPos : E} {q : E → F} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos))
    (hq : ContinuousOn q (closure (range g))) : UniformContinuous (q ∘ g) := by
  have hcompact := isCompact_closure_range_of_tendsto_atBot_atTop hg hNeg hPos
  have hqUniform := hcompact.uniformContinuousOn_of_continuous hq
  rw [← uniformContinuousOn_univ]
  exact hqUniform.comp
    (uniformContinuous_of_tendsto_atBot_atTop hg hNeg hPos).uniformContinuousOn
    (fun x _ => subset_closure ⟨x, rfl⟩)

/-- Under the same local continuity hypothesis, the postcomposition has bounded range. -/
theorem isBounded_range_comp_of_continuousOn_closure_range
    [ProperSpace E] {g : ℝ → E} {gNeg gPos : E} {q : E → F} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos))
    (hq : ContinuousOn q (closure (range g))) : IsBounded (range (q ∘ g)) := by
  have hcompact := isCompact_closure_range_of_tendsto_atBot_atTop hg hNeg hPos
  apply (hcompact.image_of_continuousOn hq).isBounded.subset
  rintro _ ⟨x, rfl⟩
  exact ⟨g x, subset_closure ⟨x, rfl⟩, rfl⟩

end Composition

section BundledComposition

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]

/-- Bundle a continuous coefficient map evaluated along a two-ended profile as a `BUC` function. -/
@[expose]
def BUC.ofTwoEndedComp {g : ℝ → E} {gNeg gPos : E} {q : E → F} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos))
    (hq : Continuous q) : BUC ℝ F :=
  BUC.ofTwoEnded (hq.comp hg) (hq.continuousAt.tendsto.comp hNeg)
    (hq.continuousAt.tendsto.comp hPos)

@[simp]
theorem BUC.ofTwoEndedComp_apply {g : ℝ → E} {gNeg gPos : E} {q : E → F}
    (hg : Continuous g) (hNeg : Tendsto g atBot (𝓝 gNeg))
    (hPos : Tendsto g atTop (𝓝 gPos)) (hq : Continuous q) (z : ℝ) :
    BUC.ofTwoEndedComp hg hNeg hPos hq z = q (g z) := rfl

end BundledComposition

section BundledLocalComposition

variable {E F : Type*} [PseudoMetricSpace E] [ProperSpace E] [NormedAddCommGroup F]

/-- Bundle a coefficient map that is continuous only on the compact closure of the two-ended
profile's range. -/
@[expose]
def BUC.ofTwoEndedCompOn {g : ℝ → E} {gNeg gPos : E} {q : E → F} (hg : Continuous g)
    (hNeg : Tendsto g atBot (𝓝 gNeg)) (hPos : Tendsto g atTop (𝓝 gPos))
    (hq : ContinuousOn q (closure (range g))) : BUC ℝ F where
  toBCF :=
    { toFun := q ∘ g
      continuous_toFun := by
        rw [← continuousOn_univ]
        exact hq.comp hg.continuousOn (fun x _ => subset_closure ⟨x, rfl⟩)
      map_bounded' := Metric.isBounded_range_iff.mp
        (isBounded_range_comp_of_continuousOn_closure_range hg hNeg hPos hq) }
  uniformContinuous' := by
    change UniformContinuous (q ∘ g)
    exact uniformContinuous_comp_of_continuousOn_closure_range
      (E := E) (F := F) hg hNeg hPos hq

@[simp]
theorem BUC.ofTwoEndedCompOn_apply {g : ℝ → E} {gNeg gPos : E} {q : E → F}
    (hg : Continuous g) (hNeg : Tendsto g atBot (𝓝 gNeg))
    (hPos : Tendsto g atTop (𝓝 gPos)) (hq : ContinuousOn q (closure (range g))) (z : ℝ) :
    BUC.ofTwoEndedCompOn hg hNeg hPos hq z = q (g z) := rfl

end BundledLocalComposition

section FDerivAlongProfile

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a `C¹` map, evaluated along a continuous profile with two end states, is a
bounded uniformly continuous family of continuous linear maps.  Any continuous operation on
continuous linear maps (such as finite-dimensional complexification) can subsequently be applied
using `BUC.ofTwoEndedComp`. -/
@[expose]
noncomputable def BUC.fderivAlongTwoEnded
    {g : ℝ → E} {gNeg gPos : E} {f : E → F} {n : ℕ∞ω}
    (hg : Continuous g) (hNeg : Tendsto g atBot (𝓝 gNeg))
    (hPos : Tendsto g atTop (𝓝 gPos)) (hf : ContDiff 𝕜 n f) (hn : n ≠ 0) :
    BUC ℝ (E →L[𝕜] F) :=
  BUC.ofTwoEndedComp hg hNeg hPos (hf.continuous_fderiv hn)

@[simp]
theorem BUC.fderivAlongTwoEnded_apply {g : ℝ → E} {gNeg gPos : E} {f : E → F}
    {n : ℕ∞ω} (hg : Continuous g) (hNeg : Tendsto g atBot (𝓝 gNeg))
    (hPos : Tendsto g atTop (𝓝 gPos)) (hf : ContDiff 𝕜 n f) (hn : n ≠ 0) (z : ℝ) :
    BUC.fderivAlongTwoEnded hg hNeg hPos hf hn z = fderiv 𝕜 f (g z) := rfl

end FDerivAlongProfile

end Planarwave
