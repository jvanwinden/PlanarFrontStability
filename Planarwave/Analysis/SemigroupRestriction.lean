/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator

@[expose] public section

/-!
# Restriction of a semigroup to an invariant closed subspace

The norm and generator relation are inherited from the ambient space. This is the
restriction used for the complementary spectral subspace in Lemma 2.3.
-/

open Set

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A strongly continuous semigroup on an invariant complete submodule. -/
def restrictInvariant (S : C0Semigroup ℂ E) (K : Submodule ℂ E) [CompleteSpace K]
    (hK : ∀ t : NNReal, ∀ x ∈ K, S t x ∈ K) : C0Semigroup ℂ K where
  toFun t := ((S t).comp K.subtypeL).codRestrict K (fun x ↦ hK t x x.property)
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact S.zero_apply x
  map_add' s t := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact S.add_apply s t x
  strongContinuous' x := (S.strongContinuous (x : E)).subtype_mk _

@[simp]
theorem restrictInvariant_apply_coe (S : C0Semigroup ℂ E) (K : Submodule ℂ E)
    [CompleteSpace K] (hK : ∀ t : NNReal, ∀ x ∈ K, S t x ∈ K) (t : NNReal) (x : K) :
    (S.restrictInvariant K hK t x : E) = S t x := rfl

/-- Both inclusions of the generator domain are inherited under restriction. -/
theorem restrictInvariant_hasGeneratorAt_iff (S : C0Semigroup ℂ E)
    (K : Submodule ℂ E) [CompleteSpace K]
    (hK : ∀ t : NNReal, ∀ x ∈ K, S t x ∈ K) (x y : K) :
    (S.restrictInvariant K hK).HasGeneratorAt x y ↔ S.HasGeneratorAt (x : E) (y : E) := by
  simp only [HasGeneratorAt, hasDerivWithinAt_iff_tendsto]
  rfl

/-- A restricted bound gives the bound for the ambient semigroup after any map into the
invariant subspace. In particular this applies to the complementary spectral projection. -/
theorem norm_comp_le_restrictInvariant (S : C0Semigroup ℂ E)
    (K : Submodule ℂ E) [CompleteSpace K]
    (hK : ∀ t : NNReal, ∀ x ∈ K, S t x ∈ K)
    (Q : E →L[ℂ] E) (hQ : ∀ x, Q x ∈ K) (t : NNReal) :
    ‖(S t).comp Q‖ ≤ ‖S.restrictInvariant K hK t‖ * ‖Q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  calc
    ‖S t (Q x)‖ = ‖S.restrictInvariant K hK t ⟨Q x, hQ x⟩‖ := rfl
    _ ≤ ‖S.restrictInvariant K hK t‖ * ‖Q x‖ :=
      (S.restrictInvariant K hK t).le_opNorm _
    _ ≤ ‖S.restrictInvariant K hK t‖ * (‖Q‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (Q.le_opNorm x) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end

end C0Semigroup
