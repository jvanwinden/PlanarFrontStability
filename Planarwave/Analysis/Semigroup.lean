/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Strongly continuous semigroups

This file gives a small project-local interface for strongly continuous (`C₀`) semigroups of
continuous linear operators on a Banach space.  Time is `ℝ≥0`; using nonnegative time makes the
semigroup law and its growth consequences available without extending the semigroup to a group.

The main analytic consequence proved here is the standard exponential operator-norm bound.  Strong
continuity first gives pointwise boundedness on compact time intervals, Banach--Steinhaus upgrades
this to a uniform operator-norm bound, and the semigroup law propagates the bound to all times.
-/

open Set

universe u v

noncomputable section

/-- A strongly continuous one-parameter semigroup of continuous linear endomorphisms.

The convention for composition is `S (s + t) = (S s).comp (S t)`.  Since time addition is
commutative, the operators in the family commute as a consequence. -/
structure C0Semigroup (𝕜 : Type u) (E : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- The operator at time `t`. -/
  toFun : NNReal → E →L[𝕜] E
  /-- The operator at time zero is the identity. -/
  map_zero' : toFun 0 = ContinuousLinearMap.id 𝕜 E
  /-- The semigroup law. -/
  map_add' : ∀ s t, toFun (s + t) = (toFun s).comp (toFun t)
  /-- Every orbit is continuous in time (strong continuity). -/
  strongContinuous' : ∀ x, Continuous fun t ↦ toFun t x

namespace C0Semigroup

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

instance instFunLike : FunLike (C0Semigroup 𝕜 E) NNReal (E →L[𝕜] E) where
  coe S := S.toFun
  coe_injective S T h := by
    cases S
    cases T
    congr

@[ext]
theorem ext {S T : C0Semigroup 𝕜 E} (h : ∀ t, S t = T t) : S = T :=
  DFunLike.ext S T h

/-- The operator at time zero. -/
@[simp]
theorem map_zero (S : C0Semigroup 𝕜 E) : S 0 = ContinuousLinearMap.id 𝕜 E :=
  S.map_zero'

/-- The semigroup law. -/
theorem map_add (S : C0Semigroup 𝕜 E) (s t : NNReal) :
    S (s + t) = (S s).comp (S t) :=
  S.map_add' s t

@[simp]
theorem zero_apply (S : C0Semigroup 𝕜 E) (x : E) : S 0 x = x := by
  rw [S.map_zero]
  rfl

theorem add_apply (S : C0Semigroup 𝕜 E) (s t : NNReal) (x : E) :
    S (s + t) x = S s (S t x) := by
  rw [S.map_add]
  rfl

/-- Operators belonging to the same one-parameter semigroup commute. -/
theorem commute (S : C0Semigroup 𝕜 E) (s t : NNReal) :
    (S s).comp (S t) = (S t).comp (S s) := by
  rw [← S.map_add, add_comm, S.map_add]

/-- Strong continuity of an orbit. -/
protected theorem strongContinuous (S : C0Semigroup 𝕜 E) (x : E) :
    Continuous fun t ↦ S t x :=
  S.strongContinuous' x

/-- Continuity of the norm of an orbit. -/
theorem continuous_norm_apply (S : C0Semigroup 𝕜 E) (x : E) :
    Continuous fun t ↦ ‖S t x‖ :=
  (S.strongContinuous x).norm

/-- Strong continuity at time zero, in filter form. -/
theorem tendsto_zero (S : C0Semigroup 𝕜 E) (x : E) :
    Filter.Tendsto (fun t ↦ S t x) (nhds 0) (nhds x) := by
  have h : ContinuousAt (fun t : NNReal ↦ S t x) 0 := (S.strongContinuous x).continuousAt
  have h' : Filter.Tendsto (fun t : NNReal ↦ S t x) (nhds 0) (nhds (S 0 x)) := h
  simpa only [zero_apply] using h'

/-- Every orbit is bounded on a compact time interval. -/
theorem exists_orbit_bound (S : C0Semigroup 𝕜 E) (T : NNReal) (x : E) :
    ∃ C : ℝ, ∀ t ≤ T, ‖S t x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (S.strongContinuous x).continuousOn
  exact ⟨C, fun t ht ↦ hC t ⟨bot_le, ht⟩⟩

/-- Strong continuity and completeness imply a uniform operator-norm bound on every compact
time interval.  This is the uniform boundedness principle (Banach--Steinhaus). -/
theorem exists_local_bound (S : C0Semigroup 𝕜 E) (T : NNReal) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t ≤ T, ‖S t‖ ≤ M := by
  let I := Set.Icc (0 : NNReal) T
  have hpoint : ∀ x : E, ∃ C : ℝ, ∀ t : I, ‖S t x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := S.exists_orbit_bound T x
    exact ⟨C, fun t ↦ hC t t.2.2⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : I ↦ S t) hpoint
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro t ht
  exact (hC ⟨t, bot_le, ht⟩).trans (le_max_left _ _)

/-- Iterating the semigroup law bounds the operator at an integral multiple of a time by a power
of the operator norm at that time. -/
theorem norm_nsmul_le (S : C0Semigroup 𝕜 E) (t : NNReal) :
    ∀ n : ℕ, ‖S (n • t)‖ ≤ ‖S t‖ ^ n
  | 0 => by
      simpa using (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E))
  | n + 1 => by
      calc
        ‖S ((n + 1) • t)‖ = ‖(S (n • t)).comp (S t)‖ := by rw [succ_nsmul, S.map_add]
        _ ≤ ‖S (n • t)‖ * ‖S t‖ := (S (n • t)).opNorm_comp_le (S t)
        _ ≤ ‖S t‖ ^ n * ‖S t‖ :=
          mul_le_mul_of_nonneg_right (norm_nsmul_le S t n) (norm_nonneg _)
        _ = ‖S t‖ ^ (n + 1) := (pow_succ _ n).symm

/-- A local bound on `[0, 1]` propagates to a floor-power bound at every nonnegative time. -/
theorem norm_le_floor_power (S : C0Semigroup 𝕜 E) {M : ℝ} (_hM : 1 ≤ M)
    (hlocal : ∀ t : NNReal, t ≤ 1 → ‖S t‖ ≤ M) (t : NNReal) :
    ‖S t‖ ≤ M ^ (⌊t⌋₊ + 1) := by
  let n : ℕ := ⌊t⌋₊
  let r : NNReal := t - (n : NNReal)
  have hn : (n : NNReal) ≤ t := Nat.floor_le bot_le
  have hr : r ≤ 1 := by
    rw [show r = t - (n : NNReal) from rfl, tsub_le_iff_right]
    simpa [n, add_comm] using (Nat.lt_floor_add_one t).le
  have hdecomp : (n : NNReal) + r = t := by
    exact add_tsub_cancel_of_le hn
  calc
    ‖S t‖ = ‖(S (n : NNReal)).comp (S r)‖ := by rw [← hdecomp, S.map_add]
    _ ≤ ‖S (n : NNReal)‖ * ‖S r‖ := (S (n : NNReal)).opNorm_comp_le (S r)
    _ ≤ ‖S 1‖ ^ n * ‖S r‖ := by
      gcongr
      simpa [nsmul_eq_mul] using S.norm_nsmul_le (1 : NNReal) n
    _ ≤ M ^ n * M := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hlocal 1 le_rfl) n)
      (hlocal r hr) (norm_nonneg _) (pow_nonneg (le_trans (norm_nonneg _) (hlocal 1 le_rfl)) _)
    _ = M ^ (⌊t⌋₊ + 1) := by simp [n, pow_succ]

/-- Every strongly continuous semigroup on a Banach space is exponentially bounded in operator
norm: `‖S t‖ ≤ M * exp (ω t)` for some `M ≥ 1` and `ω ≥ 0`. -/
theorem exists_exponential_bound (S : C0Semigroup 𝕜 E) :
    ∃ M ω : ℝ, 1 ≤ M ∧ 0 ≤ ω ∧ ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t) := by
  obtain ⟨M, hM, hlocal⟩ := S.exists_local_bound 1
  refine ⟨M, Real.log M, hM, Real.log_nonneg hM, ?_⟩
  intro t
  calc
    ‖S t‖ ≤ M ^ (⌊t⌋₊ + 1) := S.norm_le_floor_power hM hlocal t
    _ = M * M ^ ⌊t⌋₊ := by rw [pow_succ, mul_comm]
    _ = M * M ^ (⌊t⌋₊ : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ M * M ^ (t : ℝ) := by
      gcongr
      exact_mod_cast Nat.floor_le (a := t) bot_le
    _ = M * Real.exp (Real.log M * t) := by
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hM)]

/-- The identity semigroup. -/
def id : C0Semigroup 𝕜 E where
  toFun := fun _ ↦ ContinuousLinearMap.id 𝕜 E
  map_zero' := rfl
  map_add' := by simp
  strongContinuous' := fun x ↦ continuous_const

@[simp]
theorem id_apply (t : NNReal) (x : E) : id (𝕜 := 𝕜) (E := E) t x = x := rfl

/-- The contraction property for a strongly continuous semigroup. -/
def IsContraction (S : C0Semigroup 𝕜 E) : Prop :=
  ∀ t, ‖S t‖ ≤ 1

theorem isContraction_iff_norm_apply_le (S : C0Semigroup 𝕜 E) :
    S.IsContraction ↔ ∀ t x, ‖S t x‖ ≤ ‖x‖ := by
  constructor
  · intro h t x
    calc
      ‖S t x‖ ≤ ‖S t‖ * ‖x‖ := (S t).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (h t) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  · intro h t
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa using h t x

end C0Semigroup

/-- A strongly continuous contraction semigroup. -/
structure ContractionSemigroup (𝕜 : Type u) (E : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- The underlying strongly continuous semigroup. -/
  toC0Semigroup : C0Semigroup 𝕜 E
  /-- Every operator has norm at most one. -/
  isContraction' : toC0Semigroup.IsContraction

namespace ContractionSemigroup

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

instance instFunLike : FunLike (ContractionSemigroup 𝕜 E) NNReal (E →L[𝕜] E) where
  coe S := S.toC0Semigroup
  coe_injective S T h := by
    cases S with
    | mk S hS =>
      cases T with
      | mk T hT =>
        have hST : S = T := DFunLike.coe_injective h
        subst T
        rfl

instance instCoeC0Semigroup : Coe (ContractionSemigroup 𝕜 E) (C0Semigroup 𝕜 E) :=
  ⟨toC0Semigroup⟩

@[ext]
theorem ext {S T : ContractionSemigroup 𝕜 E} (h : ∀ t, S t = T t) : S = T :=
  DFunLike.ext S T h

@[simp]
theorem map_zero (S : ContractionSemigroup 𝕜 E) :
    S 0 = ContinuousLinearMap.id 𝕜 E :=
  S.toC0Semigroup.map_zero

@[simp]
theorem zero_apply (S : ContractionSemigroup 𝕜 E) (x : E) : S 0 x = x :=
  S.toC0Semigroup.zero_apply x

theorem map_add (S : ContractionSemigroup 𝕜 E) (s t : NNReal) :
    S (s + t) = (S s).comp (S t) :=
  S.toC0Semigroup.map_add s t

theorem add_apply (S : ContractionSemigroup 𝕜 E) (s t : NNReal) (x : E) :
    S (s + t) x = S s (S t x) :=
  S.toC0Semigroup.add_apply s t x

protected theorem strongContinuous (S : ContractionSemigroup 𝕜 E) (x : E) :
    Continuous fun t ↦ S t x :=
  S.toC0Semigroup.strongContinuous x

theorem tendsto_zero (S : ContractionSemigroup 𝕜 E) (x : E) :
    Filter.Tendsto (fun t ↦ S t x) (nhds 0) (nhds x) :=
  S.toC0Semigroup.tendsto_zero x

/-- The defining operator-norm contraction estimate. -/
theorem norm_le_one (S : ContractionSemigroup 𝕜 E) (t : NNReal) : ‖S t‖ ≤ 1 :=
  S.isContraction' t

/-- The pointwise contraction estimate. -/
theorem norm_apply_le (S : ContractionSemigroup 𝕜 E) (t : NNReal) (x : E) :
    ‖S t x‖ ≤ ‖x‖ :=
  S.toC0Semigroup.isContraction_iff_norm_apply_le.mp S.isContraction' t x

/-- Package a `C₀` semigroup together with a pointwise contraction estimate. -/
def ofNormApplyLE (S : C0Semigroup 𝕜 E) (h : ∀ t x, ‖S t x‖ ≤ ‖x‖) :
    ContractionSemigroup 𝕜 E :=
  ⟨S, S.isContraction_iff_norm_apply_le.mpr h⟩

/-- The identity contraction semigroup. -/
def id : ContractionSemigroup 𝕜 E :=
  ⟨C0Semigroup.id, fun _ ↦ ContinuousLinearMap.norm_id_le⟩

@[simp]
theorem id_apply (t : NNReal) (x : E) : id (𝕜 := 𝕜) (E := E) t x = x := rfl

end ContractionSemigroup
