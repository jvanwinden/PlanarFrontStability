/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ClosedOperator

@[expose] public section

/-!
# Closedness from one resolvent point

For the common-domain family in Section 2 of the paper, closedness need not be proved by a
separate interpolation estimate.  Once one resolvent map `A - z I` is bijective, the Banach
inverse theorem makes its inverse continuous, and the graph of `A` is the zero set of a continuous
map.  This is the standard resolvent proof that a densely defined operator with a nonempty
resolvent set is closed.
-/

open Function Set

universe u v w

noncomputable section

namespace Planarwave

variable {𝕜 : Type u} {X : Type v} {Dom : Type w}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Dom] [NormedSpace 𝕜 Dom] [CompleteSpace Dom]

/-- If one member `A - z I` of the resolvent pencil is bijective, then the graph of `A` is
closed.  The domain inclusion need not be assumed injective for this closedness statement. -/
theorem isClosed_range_inclusion_prod_operator_of_bijective_resolvent
    (inclusion operator : Dom →L[𝕜] X) (z : 𝕜)
    (hres : Bijective (operator - z • inclusion)) :
    IsClosed (range (inclusion.prod operator)) := by
  let B : Dom →L[𝕜] X := operator - z • inclusion
  let e : Dom ≃L[𝕜] X := ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr hres.injective) (LinearMap.range_eq_top.mpr hres.surjective)
  let R : X →L[𝕜] Dom := e.symm
  have he_apply (x : Dom) : e x = B x := rfl
  have hgraph :
      range (inclusion.prod operator) =
        {p : X × X | inclusion (R (p.2 - z • p.1)) = p.1} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      change inclusion (R (operator x - z • inclusion x)) = inclusion x
      change inclusion (R (B x)) = inclusion x
      change inclusion (e.symm (e x)) = inclusion x
      rw [e.symm_apply_apply]
    · intro hp
      let x : Dom := R (p.2 - z • p.1)
      have hfirst : inclusion x = p.1 := hp
      have hresolvent : B x = p.2 - z • p.1 := by
        change e (e.symm (p.2 - z • p.1)) = p.2 - z • p.1
        exact e.apply_symm_apply _
      have hsecond : operator x = p.2 := by
        change operator x - z • inclusion x = p.2 - z • p.1 at hresolvent
        rw [hfirst] at hresolvent
        exact sub_left_injective hresolvent
      exact ⟨x, Prod.ext hfirst hsecond⟩
  rw [hgraph]
  exact isClosed_eq (by fun_prop) continuous_fst

/-- Package a common-domain operator as a `ClosedOperator` using any known resolvent point. -/
def ClosedOperator.ofBijectiveResolvent
    (inclusion operator : Dom →L[𝕜] X) (hinclusion : Injective inclusion)
    (z : 𝕜) (hres : Bijective (operator - z • inclusion)) :
    ClosedOperator 𝕜 X Dom where
  inclusion := inclusion
  inclusion_injective := hinclusion
  operator := operator
  isClosed_graph :=
    isClosed_range_inclusion_prod_operator_of_bijective_resolvent inclusion operator z hres

@[simp]
theorem ClosedOperator.ofBijectiveResolvent_inclusion
    (inclusion operator : Dom →L[𝕜] X) (hinclusion : Injective inclusion)
    (z : 𝕜) (hres : Bijective (operator - z • inclusion)) :
    (ClosedOperator.ofBijectiveResolvent inclusion operator hinclusion z hres).inclusion = inclusion :=
  rfl

@[simp]
theorem ClosedOperator.ofBijectiveResolvent_operator
    (inclusion operator : Dom →L[𝕜] X) (hinclusion : Injective inclusion)
    (z : 𝕜) (hres : Bijective (operator - z • inclusion)) :
    (ClosedOperator.ofBijectiveResolvent inclusion operator hinclusion z hres).operator = operator :=
  rfl

end Planarwave
