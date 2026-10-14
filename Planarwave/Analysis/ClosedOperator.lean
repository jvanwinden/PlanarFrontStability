/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section

/-!
# Closed operators with a fixed graph-norm domain

This file provides a small interface for the unbounded operators used in the linear analysis of
the planar-front problem.  Rather than attempting to put a norm on a partially defined map, we
bundle its common graph-norm domain as a Banach space `Dom`.  The continuous linear map
`inclusion : Dom →L[𝕜] X` remembers the underlying vector in the ambient Banach space, while
`operator : Dom →L[𝕜] X` is the operator on that domain.

The graph is required to be closed in `X × X`.  The graph norm itself is not prescribed: concrete
applications may use any equivalent Banach norm on `Dom` for which `inclusion` and `operator` are
continuous.

For the sign convention used in `Challenge`, the resolvent map at `λ` is
`operator - λ • inclusion`.  Membership in the resolvent set is defined algebraically by bijectivity.
Because both the graph-norm domain and the ambient space are Banach, Mathlib's Banach inverse
theorem upgrades a bijective resolvent map to a continuous linear equivalence and hence produces
a bounded inverse.
-/

open Function Set

universe u v w

noncomputable section

namespace Planarwave

/-- A closed operator on `X`, represented on a fixed Banach graph-norm domain `Dom`.

Families of operators with a common domain are simply functions into
`ClosedOperator 𝕜 X Dom`; sharing the `Dom` parameter forces the domain and its norm to be the same
for every member of the family. -/
structure ClosedOperator (𝕜 : Type u) (X : Type v) (Dom : Type w)
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Dom] [NormedSpace 𝕜 Dom] [CompleteSpace Dom] where
  /-- Inclusion of the graph-norm domain into the ambient space. -/
  inclusion : Dom →L[𝕜] X
  /-- Distinct domain elements represent distinct ambient vectors. -/
  inclusion_injective : Injective inclusion
  /-- The operator, continuous from the graph-norm domain to the ambient space. -/
  operator : Dom →L[𝕜] X
  /-- Closedness of the operator graph in the ambient product space. -/
  isClosed_graph : IsClosed (range (inclusion.prod operator))

namespace ClosedOperator

variable {𝕜 : Type u} {X : Type v} {Dom : Type w}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Dom] [NormedSpace 𝕜 Dom] [CompleteSpace Dom]

/-- The graph map `x ↦ (x, A x)` associated with a closed operator. -/
def graphMap (A : ClosedOperator 𝕜 X Dom) : Dom →L[𝕜] X × X :=
  A.inclusion.prod A.operator

@[simp]
theorem graphMap_apply (A : ClosedOperator 𝕜 X Dom) (x : Dom) :
    A.graphMap x = (A.inclusion x, A.operator x) :=
  rfl

/-- The graph map is injective because the domain inclusion is injective. -/
theorem graphMap_injective (A : ClosedOperator 𝕜 X Dom) : Injective A.graphMap := by
  intro x y hxy
  apply A.inclusion_injective
  exact congrArg Prod.fst hxy

/-- Restatement of the bundled closed-graph property in terms of `graphMap`. -/
theorem isClosed_range_graphMap (A : ClosedOperator 𝕜 X Dom) :
    IsClosed (range A.graphMap) :=
  A.isClosed_graph

/-- The map `A - λ I` on the fixed domain.  This sign agrees with the resolvent equation in
`Challenge`. -/
def resolventMap (A : ClosedOperator 𝕜 X Dom) (z : 𝕜) : Dom →L[𝕜] X :=
  A.operator - z • A.inclusion

@[simp]
theorem resolventMap_apply (A : ClosedOperator 𝕜 X Dom) (z : 𝕜) (x : Dom) :
    A.resolventMap z x = A.operator x - z • A.inclusion x := by
  rfl

/-- A scalar is in the resolvent set when `A - λ I` is bijective from the graph-norm domain
onto the ambient space. -/
def IsInResolvent (A : ClosedOperator 𝕜 X Dom) (z : 𝕜) : Prop :=
  Bijective (A.resolventMap z)

/-- The resolvent set of a closed operator. -/
def resolventSet (A : ClosedOperator 𝕜 X Dom) : Set 𝕜 :=
  { z | A.IsInResolvent z }

/-- The spectrum is the complement of the resolvent set. -/
def spectrum (A : ClosedOperator 𝕜 X Dom) : Set 𝕜 :=
  (A.resolventSet)ᶜ

@[simp]
theorem mem_resolventSet (A : ClosedOperator 𝕜 X Dom) (z : 𝕜) :
    z ∈ A.resolventSet ↔ A.IsInResolvent z :=
  Iff.rfl

@[simp]
theorem mem_spectrum (A : ClosedOperator 𝕜 X Dom) (z : 𝕜) :
    z ∈ A.spectrum ↔ ¬ A.IsInResolvent z := by
  rfl

/-- Bijectivity of the resolvent map is equivalent to unique solvability of every resolvent
equation.  This is the form used by `TransverseSpectrum` in `Challenge`. -/
theorem isInResolvent_iff_existsUnique (A : ClosedOperator 𝕜 X Dom) (z : 𝕜) :
    A.IsInResolvent z ↔ ∀ y : X, ∃! x : Dom, A.resolventMap z x = y := by
  constructor
  · rintro ⟨hinj, hsurj⟩ y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨x, hx, ?_⟩
    intro x' hx'
    exact hinj (hx'.trans hx.symm)
  · intro h
    constructor
    · intro x x' hxx'
      obtain ⟨w, hw, huniq⟩ := h (A.resolventMap z x)
      exact (huniq x rfl).trans (huniq x' hxx'.symm).symm
    · intro y
      obtain ⟨x, hx, -⟩ := h y
      exact ⟨x, hx⟩

/-- A bijective resolvent map, upgraded to a continuous linear equivalence by the Banach inverse
theorem. -/
noncomputable def resolventEquiv (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) : Dom ≃L[𝕜] X :=
  ContinuousLinearEquiv.ofBijective (A.resolventMap z)
    (LinearMap.ker_eq_bot.mpr hz.1) (LinearMap.range_eq_top.mpr hz.2)

@[simp]
theorem resolventEquiv_apply (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) (x : Dom) :
    A.resolventEquiv z hz x = A.resolventMap z x :=
  rfl

/-- The bounded inverse `(A - λ I)⁻¹`, valued in the graph-norm domain. -/
noncomputable def resolventInverse (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) : X →L[𝕜] Dom :=
  (A.resolventEquiv z hz).symm

@[simp]
theorem resolventInverse_resolventMap (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) (x : Dom) :
    A.resolventInverse z hz (A.resolventMap z x) = x := by
  exact (A.resolventEquiv z hz).symm_apply_apply x

@[simp]
theorem resolventMap_resolventInverse (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) (y : X) :
    A.resolventMap z (A.resolventInverse z hz y) = y := by
  exact (A.resolventEquiv z hz).apply_symm_apply y

/-- Explicit existence of a bounded two-sided inverse for a bijective resolvent map. -/
theorem exists_bounded_resolventInverse (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) :
    ∃ R : X →L[𝕜] Dom,
      (∀ x, R (A.resolventMap z x) = x) ∧
      (∀ y, A.resolventMap z (R y) = y) := by
  exact ⟨A.resolventInverse z hz, A.resolventInverse_resolventMap z hz,
    A.resolventMap_resolventInverse z hz⟩

/-- Operator-norm control for the inverse produced by the Banach inverse theorem. -/
theorem resolventInverse_norm_le (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) (y : X) :
    ‖A.resolventInverse z hz y‖ ≤ ‖A.resolventInverse z hz‖ * ‖y‖ :=
  ContinuousLinearMap.le_opNorm _ _

/-- A scalar bound for the graph-norm of the unique solution of the resolvent equation. -/
theorem exists_resolvent_bound (A : ClosedOperator 𝕜 X Dom) (z : 𝕜)
    (hz : A.IsInResolvent z) :
    ∃ C ≥ 0, ∀ y : X, ‖A.resolventInverse z hz y‖ ≤ C * ‖y‖ := by
  exact ⟨‖A.resolventInverse z hz‖, norm_nonneg _, A.resolventInverse_norm_le z hz⟩

end ClosedOperator

end Planarwave
