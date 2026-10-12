/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupIntertwining
public import Planarwave.Analysis.SemigroupPerturbationGenerator

@[expose] public section

/-!
# Intertwining bounded perturbations

A bounded map intertwining the free semigroups and the bounded coefficients
also intertwines the perturbed semigroups. This transports the transverse
translation symmetry of diffusion to the full spatial linearized front flow.
-/

namespace C0Semigroup

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Bounded perturbation preserves a compatible semigroup intertwiner. -/
theorem boundedPerturbation_intertwining (S : C0Semigroup ℂ E) (T : C0Semigroup ℂ F)
    (B : E →L[ℂ] E) (C : F →L[ℂ] F) (U : E →L[ℂ] F)
    (hU : ∀ t : NNReal, (T t).comp U = U.comp (S t))
    (hB : C.comp U = U.comp B) (t : NNReal) :
    (T.boundedPerturbation C t).comp U = U.comp (S.boundedPerturbation B t) := by
  apply comp_eq_comp_of_generator_intertwining
  intro x y hxy
  rw [boundedPerturbation_hasGeneratorAt_iff] at hxy ⊢
  have hd := (U.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hxy
  have hgen : T.HasGeneratorAt (U x) (U (y - B x)) := by
    apply hd.congr
    · intro r _
      exact congrArg (fun L : E →L[ℂ] F ↦ L x) (hU r.toNNReal)
    · simp
  have hBx : C (U x) = U (B x) := congrArg (fun L : E →L[ℂ] F ↦ L x) hB
  simpa only [map_sub, ← hBx] using hgen

/-- A symmetry commuting with both diffusion and the coefficient survives their sum. -/
theorem boundedPerturbation_comm (S : C0Semigroup ℂ E) (B U : E →L[ℂ] E)
    (hU : ∀ t : NNReal, (S t).comp U = U.comp (S t))
    (hB : B.comp U = U.comp B) (t : NNReal) :
    (S.boundedPerturbation B t).comp U = U.comp (S.boundedPerturbation B t) :=
  boundedPerturbation_intertwining S S B B U hU hB t

end

end C0Semigroup
