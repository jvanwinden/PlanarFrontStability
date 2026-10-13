/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# BUC representatives of bounded smooth derivatives

A bounded next derivative makes a spatial derivative uniformly continuous.
Thus pointwise all-order heat estimates give genuine BUC derivative fields,
not merely bounds on an unbundled derivative.
-/

namespace Planarwave

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bound on the next derivative gives uniform continuity of the current one. -/
theorem uniformContinuous_iteratedFDeriv_of_bound {f : E → F} {k : ℕ} {B : ℝ}
    (hf : ContDiff ℝ (k + 1) f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ B) :
    UniformContinuous (iteratedFDeriv ℝ k f) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  have hd : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast (Nat.lt_succ_self k))
  apply (lipschitzWith_of_nnnorm_fderiv_le (C := ⟨B, hB⟩) hd ?_).uniformContinuous
  intro x
  change ‖fderiv ℝ (iteratedFDeriv ℝ k f) x‖ ≤ B
  rw [norm_fderiv_iteratedFDeriv]
  exact hb x

/-- Bundle an actual derivative, with no loss in its supremum bound. -/
theorem exists_buc_iteratedFDeriv_of_bounds {f : E → F} {k : ℕ} {A B : ℝ}
    (hf : ContDiff ℝ (k + 1) f)
    (ha : ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ B) :
    ∃ g : BUC E (E [×k]→L[ℝ] F), (∀ x, g x = iteratedFDeriv ℝ k f x) ∧ ‖g‖ ≤ A := by
  have hu := uniformContinuous_iteratedFDeriv_of_bound hf hb
  let g : BUC E (E [×k]→L[ℝ] F) :=
    { toBCF := BoundedContinuousFunction.ofNormedAddCommGroup
        (iteratedFDeriv ℝ k f) hu.continuous A ha
      uniformContinuous' := hu }
  refine ⟨g, fun _ ↦ rfl, (BUC.norm_le ((norm_nonneg _).trans (ha 0))).mpr ?_⟩
  exact ha

end

end Planarwave
