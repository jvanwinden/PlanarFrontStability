/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section

/-!
# A simple Fredholm zero mode and its spectral projection

This file isolates the functional-analytic argument used in Proposition 2.1 of the planar-wave
paper.  The graph-norm domain `Dom` and the ambient space `X` are Banach spaces.  A continuous
inclusion `i : Dom → X`, an operator `A : Dom → X`, a zero mode `φ`, and a normalized
functional `ℓ` are assumed to satisfy the two Fredholm alternatives

* `ker A = span {φ}`;
* `A u = w` is solvable exactly when `ℓ w = 0`.

The resulting rank-one map `P w = ℓ(w) • i(φ)` splits the ambient space into the neutral
mode and the Fredholm complement.  Restricting `A` to the corresponding graph-domain complement
gives a bounded linear equivalence onto `ker ℓ` by the Banach inverse theorem.
-/

open Function

universe u v

noncomputable section

namespace Planarwave

/-- The abstract simple-zero-mode hypotheses behind Proposition 2.1.

The domain carries its graph norm, so both the inclusion and the operator are continuous.  The
closed-graph property is not separately needed once this Banach graph-domain presentation is
available. -/
structure SimpleFredholmZeroMode (X : Type u) (Dom : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom] where
  /-- Continuous inclusion of the graph-norm domain into the ambient space. -/
  inclusion : Dom →L[ℂ] X
  /-- The graph-domain inclusion represents domain elements faithfully. -/
  inclusion_injective : Injective inclusion
  /-- The operator at the distinguished spectral value zero. -/
  operator : Dom →L[ℂ] X
  /-- The simple zero eigenvector in the graph domain. -/
  mode : Dom
  /-- The adjoint functional detecting the Fredholm obstruction. -/
  functional : X →L[ℂ] ℂ
  /-- Biorthogonal normalization of the zero mode and adjoint functional. -/
  normalized : functional (inclusion mode) = 1
  /-- The zero eigenspace is one-dimensional. -/
  kernel_eq_span :
    LinearMap.ker operator.toLinearMap = Submodule.span ℂ {mode}
  /-- The Fredholm solvability alternative. -/
  solvable_iff : ∀ w : X, (∃ u : Dom, operator u = w) ↔ functional w = 0

namespace SimpleFredholmZeroMode

variable {X : Type u} {Dom : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

variable (S : SimpleFredholmZeroMode X Dom)

/-! ## The neutral projection and its algebraic splitting -/

/-- The rank-one neutral projection `P w = ℓ(w) • i(φ)`. -/
def projection : X →L[ℂ] X :=
  S.functional.smulRight (S.inclusion S.mode)

@[simp]
theorem projection_apply (w : X) :
    S.projection w = S.functional w • S.inclusion S.mode :=
  rfl

/-- The zero mode is indeed killed by the operator. -/
@[simp]
theorem operator_mode : S.operator S.mode = 0 := by
  apply LinearMap.mem_ker.mp
  rw [S.kernel_eq_span]
  exact Submodule.subset_span (Set.mem_singleton S.mode)

/-- The embedded zero mode is nonzero, as follows already from normalization. -/
theorem inclusion_mode_ne_zero : S.inclusion S.mode ≠ 0 := by
  intro hzero
  have := S.normalized
  rw [hzero, map_zero] at this
  exact zero_ne_one this

/-- Consequently the graph-domain zero mode is nonzero. -/
theorem mode_ne_zero : S.mode ≠ 0 := by
  intro hzero
  apply S.inclusion_mode_ne_zero
  rw [hzero, map_zero]

/-- The normalized adjoint functional is nonzero. -/
theorem functional_ne_zero : S.functional ≠ 0 := by
  intro hzero
  have := S.normalized
  rw [hzero, zero_apply] at this
  exact zero_ne_one this

/-- The projection fixes the embedded zero mode. -/
@[simp]
theorem projection_inclusion_mode :
    S.projection (S.inclusion S.mode) = S.inclusion S.mode := by
  rw [projection_apply, S.normalized, one_smul]

/-- The rank-one neutral map is idempotent. -/
theorem projection_idempotent (w : X) :
    S.projection (S.projection w) = S.projection w := by
  simp [projection_apply, S.normalized]

/-- The complementary part has vanishing adjoint functional. -/
theorem complement_mem_kernel_functional (w : X) :
    w - S.projection w ∈ LinearMap.ker S.functional.toLinearMap := by
  rw [LinearMap.mem_ker]
  simp [projection_apply, S.normalized]

/-! ## Fredholm range and semisimplicity -/

/-- The operator range is exactly the kernel of the adjoint functional. -/
theorem range_operator_eq_kernel_functional :
    LinearMap.range S.operator.toLinearMap =
      LinearMap.ker S.functional.toLinearMap := by
  ext w
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  exact S.solvable_iff w

/-- Every operator value satisfies the Fredholm orthogonality condition. -/
theorem functional_operator (u : Dom) : S.functional (S.operator u) = 0 :=
  (S.solvable_iff (S.operator u)).mp ⟨u, rfl⟩

/-- The embedded zero mode is not in the operator range.  This is the basic semisimplicity
statement at zero. -/
theorem inclusion_mode_not_mem_range :
    S.inclusion S.mode ∉ LinearMap.range S.operator.toLinearMap := by
  intro hmem
  rw [S.range_operator_eq_kernel_functional, LinearMap.mem_ker] at hmem
  exact one_ne_zero (S.normalized.symm.trans hmem)

/-! ## The invertible restriction on the Fredholm complement -/

/-- The graph-domain complement cut out by the pulled-back adjoint functional. -/
def domainComplement : Submodule ℂ Dom :=
  LinearMap.ker (S.functional.comp S.inclusion).toLinearMap

/-- The ambient Fredholm complement. -/
def ambientComplement : Submodule ℂ X :=
  LinearMap.ker S.functional.toLinearMap

@[simp]
theorem mem_domainComplement_iff (u : Dom) :
    u ∈ S.domainComplement ↔ S.functional (S.inclusion u) = 0 :=
  Iff.rfl

@[simp]
theorem mem_ambientComplement_iff (w : X) :
    w ∈ S.ambientComplement ↔ S.functional w = 0 :=
  Iff.rfl

/-- The operator restricted to the graph-domain complement and corestricted to `ker ℓ`. -/
def complementOperator : S.domainComplement →L[ℂ] S.ambientComplement :=
  S.operator.restrict fun u _ ↦ by
    exact S.functional_operator u

@[simp]
theorem complementOperator_apply (u : S.domainComplement) :
    (S.complementOperator u : X) = S.operator (u : Dom) :=
  rfl

/-- The restricted operator is injective. -/
theorem complementOperator_injective : Injective S.complementOperator := by
  intro u v huv
  have huv' : S.operator ((u : Dom) - (v : Dom)) = 0 := by
    have := congrArg Subtype.val huv
    simpa only [complementOperator_apply, map_sub, sub_eq_zero] using this
  have hspan : (u : Dom) - (v : Dom) ∈ Submodule.span ℂ {S.mode} := by
    rw [← S.kernel_eq_span, LinearMap.mem_ker]
    exact huv'
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  have hu0 : S.functional (S.inclusion (u : Dom)) = 0 := u.property
  have hv0 : S.functional (S.inclusion (v : Dom)) = 0 := v.property
  have hphase : S.functional (S.inclusion ((u : Dom) - (v : Dom))) = 0 := by
    rw [map_sub, map_sub, hu0, hv0, sub_self]
  have ha0 : a = 0 := by
    rw [← ha, map_smul, map_smul, S.normalized, smul_eq_mul, mul_one] at hphase
    exact hphase
  apply Subtype.ext
  apply sub_eq_zero.mp
  calc
    (u : Dom) - (v : Dom) = a • S.mode := ha.symm
    _ = 0 := by rw [ha0, zero_smul]

/-- The restricted operator is surjective.  A solution is moved into the domain complement by
subtracting its neutral component, which does not change its operator image. -/
theorem complementOperator_surjective : Surjective S.complementOperator := by
  intro w
  have hw0 : S.functional (w : X) = 0 := w.property
  obtain ⟨u, hu⟩ := (S.solvable_iff (w : X)).mpr hw0
  let a : ℂ := S.functional (S.inclusion u)
  let u₀ : Dom := u - a • S.mode
  have hu₀mem : u₀ ∈ S.domainComplement := by
    change S.functional (S.inclusion u₀) = 0
    simp only [u₀, a, map_sub, map_smul, S.normalized, smul_eq_mul, mul_one, sub_self]
  refine ⟨⟨u₀, hu₀mem⟩, ?_⟩
  apply Subtype.ext
  change S.operator u₀ = (w : X)
  simp only [u₀, map_sub, map_smul, S.operator_mode, smul_zero, sub_zero, hu]

/-- The bijective restriction upgraded, by the Banach inverse theorem, to a continuous linear
equivalence. -/
noncomputable def complementOperatorEquiv :
    S.domainComplement ≃L[ℂ] S.ambientComplement := by
  letI : CompleteSpace S.domainComplement :=
    (S.functional.comp S.inclusion).isClosed_ker.completeSpace_coe
  letI : CompleteSpace S.ambientComplement :=
    S.functional.isClosed_ker.completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective S.complementOperator
    (LinearMap.ker_eq_bot.mpr S.complementOperator_injective)
    (LinearMap.range_eq_top.mpr S.complementOperator_surjective)

@[simp]
theorem complementOperatorEquiv_apply (u : S.domainComplement) :
    S.complementOperatorEquiv u = S.complementOperator u :=
  rfl

/-- The bounded inverse of the complementary restriction. -/
noncomputable def complementInverse :
    S.ambientComplement →L[ℂ] S.domainComplement :=
  S.complementOperatorEquiv.symm

@[simp]
theorem complementInverse_complementOperator (u : S.domainComplement) :
    S.complementInverse (S.complementOperator u) = u :=
  S.complementOperatorEquiv.symm_apply_apply u

@[simp]
theorem complementOperator_complementInverse (w : S.ambientComplement) :
    S.complementOperator (S.complementInverse w) = w :=
  S.complementOperatorEquiv.apply_symm_apply w

end SimpleFredholmZeroMode

end Planarwave
