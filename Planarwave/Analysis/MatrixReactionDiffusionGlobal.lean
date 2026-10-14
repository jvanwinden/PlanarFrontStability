/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionMaximal
import all Planarwave.Analysis.MatrixReactionDiffusionContinuation

/-!
# The global-solution consequence of a uniform a priori bound

This is the continuation step in the paper's final proof: once the
nonlinear estimates bound the BUC norm throughout the maximal lifetime,
that lifetime is infinite. The resulting trajectory satisfies the exact
global solution predicate in the challenge, including joint smoothness
and uniform continuity on every finite spacetime slab.
-/

open Set Filter
open scoped ContDiff InnerProductSpace Laplacian Topology ENNReal

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

namespace IsMaximalMatrixReactionDiffusion

section Lifetime

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]
  {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} {h₁ : IsSmoothParabolic f D}
  {u₀ : BUC E (ℝ^n)} {T : ℝ≥0∞} {u : ℝ → BUC E (ℝ^n)}
  (hm : IsMaximalMatrixReactionDiffusion f D h₁ u₀ T u)

include hm

/-- A uniform norm bound rules out a finite maximal lifetime. The proof
uses the bounded-continuation theorem and maximality, as in the paper. -/
theorem lifetime_eq_top_of_bounded {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ENNReal.ofReal t < T → ‖u t‖ ≤ B) : T = ⊤ := by
  by_contra hT
  let R := T.toReal
  have hR : 0 < R := ENNReal.toReal_pos hm.positive.ne' hT
  have hTR : T = ENNReal.ofReal R := (ENNReal.ofReal_toReal hT).symm
  have hlt {t : ℝ} (ht : t < R) : ENNReal.ofReal t < T := by
    rw [hTR]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 ht
  have hu : ContinuousOn u (Ico 0 R) :=
    hm.continuous.mono (fun t ht ↦ ⟨ht.1, hlt ht.2⟩)
  have hbound : ∀ t ∈ Ico 0 R, ‖u t‖ ≤ B :=
    fun t ht ↦ hb t ht.1 (hlt ht.2)
  have hmild : ∀ S ∈ Ico 0 R,
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive S u :=
    fun S hS ↦ hm.mild S hS.1 (hlt hS.2)
  obtain ⟨S, hS, w, hw, heq, hmw, _⟩ :=
    exists_matrixReactionDiffusion_extension_of_bounded f D h₁ hR hB hu hbound hmild
  have hwinit : w 0 = u₀ := (heq ⟨le_rfl, hR⟩).symm.trans hm.initial
  have hmax := (hm.maximal S w (hR.le.trans hS.le) hw.continuousOn hwinit hmw).1
  rw [hTR] at hmax
  exact (not_lt_of_ge hS.le) ((ENNReal.ofReal_lt_ofReal_iff hR).1 hmax)

end Lifetime

section GlobalSolution

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} {h₁ : IsSmoothParabolic f D}
  {u₀ : BUC (ℝ^d) (ℝ^n)} {T : ℝ≥0∞} {u : ℝ → BUC (ℝ^d) (ℝ^n)}
  (hm : IsMaximalMatrixReactionDiffusion f D h₁ u₀ T u)

include hm

/-- An infinite maximal lifetime gives the original global classical
solution predicate, with no weakening of its spacetime requirements. -/
theorem isRDESolution_of_lifetime_top (hT : T = ⊤) :
    IsRDESolution f D (fun t x ↦ u t x) := by
  have hfinite (t : ℝ) : ENNReal.ofReal t < T := by
    rw [hT]
    exact ENNReal.ofReal_lt_top
  refine ⟨fun t _ ↦ hm.isBUCOn (hfinite t), ?_, ?_⟩
  · simpa only [hT, ENNReal.ofReal_lt_top, and_true] using! hm.contDiffOn
  · intro t ht x
    exact (hm.hasDerivAt ht (hfinite t) x).deriv

/-- The global PDE conclusion needed once the nonlinear bootstrap has
established a uniform BUC bound. -/
theorem isRDESolution_of_bounded {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ENNReal.ofReal t < T → ‖u t‖ ≤ B) :
    IsRDESolution f D (fun t x ↦ u t x) :=
  hm.isRDESolution_of_lifetime_top (hm.lifetime_eq_top_of_bounded hB hb)

end GlobalSolution

end IsMaximalMatrixReactionDiffusion

end

end Planarwave
