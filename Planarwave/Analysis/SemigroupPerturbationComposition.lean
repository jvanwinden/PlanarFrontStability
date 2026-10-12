/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupUniqueness
public import Planarwave.Analysis.SemigroupPerturbationGenerator

@[expose] public section

/-!
# Reassociation of bounded semigroup perturbations

The generator relation identifies successive perturbations with perturbation by the sum.
In particular a perturbation can be based at any member of a bounded-operator family, as
required for the neighborhood estimates in the paper's appendix.
-/

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

@[simp]
theorem boundedPerturbation_zero (S : C0Semigroup ℂ E) : S.boundedPerturbation 0 = S := by
  apply eq_of_generator_iff
  intro x y
  simp only [boundedPerturbation_hasGeneratorAt_iff, _root_.zero_apply, sub_zero]

/-- Two bounded perturbations compose by addition, on the same generator domain. -/
theorem boundedPerturbation_add (S : C0Semigroup ℂ E) (B C : E →L[ℂ] E) :
    (S.boundedPerturbation B).boundedPerturbation C = S.boundedPerturbation (B + C) := by
  apply eq_of_generator_iff
  intro x y
  simp only [boundedPerturbation_hasGeneratorAt_iff, _root_.add_apply]
  have h : y - C x - B x = y - (B x + C x) := by abel
  rw [h]

/-- Rebase the perturbation family at `B`, with perturbation `C - B`. -/
theorem boundedPerturbation_sub (S : C0Semigroup ℂ E) (B C : E →L[ℂ] E) :
    (S.boundedPerturbation B).boundedPerturbation (C - B) = S.boundedPerturbation C := by
  rw [boundedPerturbation_add]
  congr 1
  abel

end

end C0Semigroup
