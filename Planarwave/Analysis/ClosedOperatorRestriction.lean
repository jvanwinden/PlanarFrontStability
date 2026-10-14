/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ClosedOperatorResolvent
public import Planarwave.Analysis.SemigroupRestriction

@[expose] public section

/-!
# The closed operator on a complementary spectral subspace

We restrict the graph-norm domain to the inverse image of the kernel of a bounded
map. For a simple spectral projection, the Fredholm splitting removes the critical
eigenvalue from this restricted operator's spectrum. Resolvent norms are inherited
from the ambient operator at every ambient resolvent point.
-/

open Set

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

variable (A : ClosedOperator ℂ E Dom) (P : E →L[ℂ] E)

/-- The original graph-norm domain intersected with the complementary subspace. -/
abbrev kernelDomain : Submodule ℂ Dom := (P.comp A.inclusion).ker

/-- The part of `A` on `ker P`, on exactly the restricted original domain. -/
def restrictKernel (hA : ∀ v, P (A.inclusion v) = 0 → P (A.operator v) = 0) :
    ClosedOperator ℂ P.ker (A.kernelDomain P) where
  inclusion := (A.inclusion.comp (A.kernelDomain P).subtypeL).codRestrict P.ker
    (fun v ↦ v.property)
  inclusion_injective := by
    intro x y h
    exact Subtype.ext (A.inclusion_injective (congrArg Subtype.val h))
  operator := (A.operator.comp (A.kernelDomain P).subtypeL).codRestrict P.ker
    (fun v ↦ hA v v.property)
  isClosed_graph := by
    have heq : Set.range
        ((A.inclusion.comp (A.kernelDomain P).subtypeL).codRestrict P.ker
          (fun v ↦ v.property) |>.prod
        ((A.operator.comp (A.kernelDomain P).subtypeL).codRestrict P.ker
          (fun v ↦ hA v v.property))) =
        (fun p : P.ker × P.ker ↦ ((p.1 : E), (p.2 : E))) ⁻¹'
          Set.range (A.inclusion.prod A.operator) := by
      ext p
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨(v : Dom), rfl⟩
      · rintro ⟨v, hv⟩
        have hv₁ : A.inclusion v = (p.1 : E) := congrArg Prod.fst hv
        refine ⟨⟨v, ?_⟩, ?_⟩
        · change P (A.inclusion v) = 0
          rw [hv₁]
          exact p.1.property
        · apply Prod.ext <;> apply Subtype.ext
          · exact hv₁
          · exact congrArg Prod.snd hv
    rw [heq]
    exact A.isClosed_graph.preimage (by fun_prop)

@[simp]
theorem restrictKernel_inclusion_coe
    (hA : ∀ v, P (A.inclusion v) = 0 → P (A.operator v) = 0) (v : A.kernelDomain P) :
    ((A.restrictKernel P hA).inclusion v : E) = A.inclusion v := rfl

@[simp]
theorem restrictKernel_operator_coe
    (hA : ∀ v, P (A.inclusion v) = 0 → P (A.operator v) = 0) (v : A.kernelDomain P) :
    ((A.restrictKernel P hA).operator v : E) = A.operator v := rfl

@[simp]
theorem restrictKernel_resolventMap_coe
    (hA : ∀ v, P (A.inclusion v) = 0 → P (A.operator v) = 0)
    (z : ℂ) (v : A.kernelDomain P) :
    ((A.restrictKernel P hA).resolventMap z v : E) = A.resolventMap z v := rfl

/-- The restricted closed operator is the full generator of the restricted semigroup. -/
theorem restrictKernel_hasGeneratorAt_iff (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    (hS : ∀ t : NNReal, ∀ x ∈ P.ker, S t x ∈ P.ker)
    (hA : ∀ v, P (A.inclusion v) = 0 → P (A.operator v) = 0) (x y : P.ker) :
    (S.restrictInvariant P.ker hS).HasGeneratorAt x y ↔
      ∃ v, (A.restrictKernel P hA).inclusion v = x ∧
        (A.restrictKernel P hA).operator v = y := by
  rw [S.restrictInvariant_hasGeneratorAt_iff, hgen]
  constructor
  · rintro ⟨v, hx, hy⟩
    have hv : v ∈ A.kernelDomain P := by
      change P (A.inclusion v) = 0
      rw [hx]
      exact x.property
    exact ⟨⟨v, hv⟩, Subtype.ext hx, Subtype.ext hy⟩
  · rintro ⟨v, hx, hy⟩
    exact ⟨v, congrArg Subtype.val hx, congrArg Subtype.val hy⟩

variable (hA : ∀ v, P (A.inclusion v) = 0 → P (A.operator v) = 0)
  {ζ : ℂ}

/-- An ambient resolvent preserves the complement of an eigenprojection. The proof uses
the full domain lift of the projection, so it does not presume a resolvent on the subspace. -/
theorem isInResolvent_restrictKernel
    (hleft : ∀ v, P (A.operator v) = ζ • P (A.inclusion v))
    (hlift : ∀ x, ∃ v, A.inclusion v = P x ∧ A.operator v = ζ • P x)
    {z : ℂ} (hz : A.IsInResolvent z) : (A.restrictKernel P hA).IsInResolvent z := by
  constructor
  · intro v w hvw
    exact Subtype.ext (hz.1 (congrArg Subtype.val hvw))
  · intro y
    obtain ⟨v, hv⟩ := hz.2 (y : E)
    obtain ⟨u, hu, hAu⟩ := hlift (A.inclusion v)
    have hzero : A.resolventMap z u = 0 := by
      have hp : P (A.resolventMap z v) = 0 := by rw [hv]; exact y.property
      simpa only [resolventMap_apply, map_sub, map_smul, hleft, hu, hAu] using hp
    have hu0 : u = 0 := hz.1 (hzero.trans (map_zero _).symm)
    have hvK : v ∈ A.kernelDomain P := by
      change P (A.inclusion v) = 0
      rw [← hu, hu0, map_zero]
    exact ⟨⟨v, hvK⟩, Subtype.ext hv⟩

/-- At an ambient resolvent point, restriction cannot increase its norm. -/
theorem norm_ambientResolvent_restrictKernel_le
    (hleft : ∀ v, P (A.operator v) = ζ • P (A.inclusion v))
    (hlift : ∀ x, ∃ v, A.inclusion v = P x ∧ A.operator v = ζ • P x)
    {z : ℂ} (hz : A.IsInResolvent z) :
    ‖(A.restrictKernel P hA).ambientResolvent z‖ ≤ ‖A.ambientResolvent z‖ := by
  let T := A.restrictKernel P hA
  have hzT : T.IsInResolvent z := A.isInResolvent_restrictKernel P hA hleft hlift hz
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  have hv : ((T.resolventInverse z hzT y : A.kernelDomain P) : Dom) =
      A.resolventInverse z hz (y : E) := by
    apply hz.1
    exact (congrArg Subtype.val (T.resolventMap_resolventInverse z hzT y)).trans
      (A.resolventMap_resolventInverse z hz (y : E)).symm
  have heq : (T.ambientResolvent z y : E) = A.ambientResolvent z (y : E) := by
    rw [T.ambientResolvent_eq hzT, A.ambientResolvent_eq hz]
    exact congrArg A.inclusion hv
  change ‖(T.ambientResolvent z y : E)‖ ≤ _
  rw [heq]
  exact (A.ambientResolvent z).le_opNorm (y : E)

/-- The simple-eigenvalue Fredholm splitting makes the critical eigenvalue a resolvent
point on the complement. In particular, no critical spectrum is left behind there. -/
theorem isInResolvent_restrictKernel_eigenvalue
    (hP : ∀ x, P (P x) = P x)
    (hlift : ∀ x, ∃ v, A.inclusion v = P x ∧ A.operator v = ζ • P x)
    (hker : ∀ v, A.resolventMap ζ v = 0 → P (A.inclusion v) = A.inclusion v)
    (hrange : ∀ y, P y = 0 → ∃ v, A.resolventMap ζ v = y) :
    (A.restrictKernel P hA).IsInResolvent ζ := by
  constructor
  · intro v w hvw
    have hzero : A.resolventMap ζ ((v : Dom) - w) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hvw)
    have hi := hker ((v : Dom) - w) hzero
    have hPv : P (A.inclusion v) = 0 := v.property
    have hPw : P (A.inclusion w) = 0 := w.property
    rw [map_sub, map_sub, hPv, hPw, sub_self] at hi
    exact Subtype.ext (A.inclusion_injective (sub_eq_zero.mp hi.symm))
  · intro y
    obtain ⟨v, hv⟩ := hrange y y.property
    obtain ⟨u, hu, hAu⟩ := hlift (A.inclusion v)
    have hvK : v - u ∈ A.kernelDomain P := by
      change P (A.inclusion (v - u)) = 0
      rw [map_sub, map_sub, hu, hP, sub_self]
    refine ⟨⟨v - u, hvK⟩, Subtype.ext ?_⟩
    change A.resolventMap ζ (v - u) = (y : E)
    rw [map_sub, hv, resolventMap_apply, hu, hAu, sub_self, sub_zero]

/-- Spectral removal: the restricted spectrum is contained in the ambient spectrum
with the simple critical eigenvalue deleted. -/
theorem spectrum_restrictKernel_subset
    (hP : ∀ x, P (P x) = P x)
    (hleft : ∀ v, P (A.operator v) = ζ • P (A.inclusion v))
    (hlift : ∀ x, ∃ v, A.inclusion v = P x ∧ A.operator v = ζ • P x)
    (hker : ∀ v, A.resolventMap ζ v = 0 → P (A.inclusion v) = A.inclusion v)
    (hrange : ∀ y, P y = 0 → ∃ v, A.resolventMap ζ v = y) :
    (A.restrictKernel P hA).spectrum ⊆ A.spectrum \ {ζ} := by
  intro z hz
  constructor
  · by_contra h
    exact hz (A.isInResolvent_restrictKernel P hA hleft hlift (not_not.mp h))
  · intro h
    exact hz (h ▸ A.isInResolvent_restrictKernel_eigenvalue P hA hP hlift hker hrange)

end

end Planarwave.ClosedOperator
