/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupPerturbation
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Holomorphic dependence on a bounded perturbation

At each fixed time, the bounded-perturbation semigroup is holomorphic in its
coefficient, in operator norm. On a finite time interval the Volterra operator
depends continuously linearly on that coefficient, and its complementary operator
`I - V` is invertible for every coefficient by the factorial Volterra estimate.
Holomorphy of inversion and bounded evaluation of paths give the result.

This is parameter analyticity, distinct from time analyticity. It supplies the
holomorphic Fourier symbol required for Section 3's contour shift.
-/

open MeasureTheory Set
open scoped ContDiff

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Volterra operator is linear in the bounded perturbation coefficient. -/
theorem perturbationOperator_add_coefficient (S : C0Semigroup ℂ E)
    (B C : E →L[ℂ] E) (T : NNReal) :
    S.perturbationOperator (B + C) T = S.perturbationOperator B T + S.perturbationOperator C T := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousMap.ext
  intro t
  exact S.duhamel_add (B.continuous.comp (continuous_extendTimePath u))
    (C.continuous.comp (continuous_extendTimePath u)) t

theorem perturbationOperator_smul_coefficient (S : C0Semigroup ℂ E)
    (a : ℂ) (B : E →L[ℂ] E) (T : NNReal) :
    S.perturbationOperator (a • B) T = a • S.perturbationOperator B T := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousMap.ext
  intro t
  exact S.duhamel_smul a (fun r ↦ B (extendTimePath u r)) t

set_option maxHeartbeats 800000 in
/-- Coefficient dependence of the path-space Volterra operator, as a bounded linear map. -/
def perturbationCoefficientCLM (S : C0Semigroup ℂ E) (T : NNReal) :
    (E →L[ℂ] E) →L[ℂ] (TimePath (E := E) T →L[ℂ] TimePath (E := E) T) := by
  let M := (S.exists_local_bound T).choose
  have hM := (S.exists_local_bound T).choose_spec
  refine LinearMap.mkContinuous
    { toFun := fun B ↦ S.perturbationOperator B T
      map_add' := fun B C ↦ S.perturbationOperator_add_coefficient B C T
      map_smul' := by
        intro a B
        change S.perturbationOperator (a • B) T = a • S.perturbationOperator B T
        exact S.perturbationOperator_smul_coefficient a B T }
    (M * (T : ℝ)) ?_
  intro B
  simpa only [M, LinearMap.coe_mk, AddHom.coe_mk, mul_right_comm] using!
    S.norm_perturbationOperator_le B T (zero_le_one.trans hM.1) hM.2

@[simp]
theorem perturbationCoefficientCLM_apply (S : C0Semigroup ℂ E) (T : NNReal) (B : E →L[ℂ] E) :
    S.perturbationCoefficientCLM T B = S.perturbationOperator B T := rfl

/-- The Volterra complement is invertible at every bounded coefficient, not merely near zero. -/
theorem one_sub_perturbationOperator_isInvertible (S : C0Semigroup ℂ E)
    (B : E →L[ℂ] E) (T : NNReal) :
    (1 - S.perturbationOperator B T).IsInvertible := by
  have h := ContinuousLinearMap.isUnit_iff_bijective.mp (S.isUnit_one_sub_perturbationOperator B T)
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr h.1)
    (LinearMap.range_eq_top.mpr h.2), rfl⟩

/-- The previously constructed Volterra series is exactly the bounded inverse. -/
theorem volterraInverse_eq_inverse (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal) :
    S.volterraInverse B T = (1 - S.perturbationOperator B T).inverse := by
  have h := S.one_sub_perturbationOperator_isInvertible B T
  apply ContinuousLinearMap.ext
  intro u
  apply h.injective
  exact (S.volterraInverse_sub B T u).trans (h.self_apply_inverse u).symm

set_option maxHeartbeats 800000 in
/-- Holomorphy of the full path-space solution inverse in its coefficient. -/
theorem contDiff_volterraInverse_coefficient (S : C0Semigroup ℂ E) (T : NNReal) :
    ContDiff ℂ ω (fun B : E →L[ℂ] E ↦ S.volterraInverse B T) := by
  have heq : (fun B : E →L[ℂ] E ↦ S.volterraInverse B T) =
      (fun B ↦ (1 - S.perturbationOperator B T).inverse) :=
    funext fun B ↦ S.volterraInverse_eq_inverse B T
  rw [heq]
  apply contDiff_iff_contDiffAt.mpr
  intro B
  have hlin : ContDiffAt ℂ ω
      (fun C : E →L[ℂ] E ↦ 1 - S.perturbationOperator C T) B := by
    have hV : ContDiff ℂ ω (S.perturbationCoefficientCLM T) := by
      exact ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := E →L[ℂ] E)
        (F := TimePath (E := E) T →L[ℂ] TimePath (E := E) T) (S.perturbationCoefficientCLM T)
    simpa only [perturbationCoefficientCLM_apply] using
      (contDiff_const.sub hV).contDiffAt (x := B)
  exact (S.one_sub_perturbationOperator_isInvertible B T).contDiffAt_map_inverse.comp B hlin

/-- Entire operator-norm dependence of the perturbed semigroup at each fixed time. -/
theorem contDiff_boundedPerturbation_coefficient (S : C0Semigroup ℂ E) (t : NNReal) :
    ContDiff ℂ ω (fun B : E →L[ℂ] E ↦ S.boundedPerturbation B t) := by
  change ContDiff ℂ ω (fun B : E →L[ℂ] E ↦
    (ContinuousMap.evalCLM ℂ ⟨(t : ℝ), t.2, le_rfl⟩).comp
      ((S.volterraInverse B t).comp (S.freePathOperator t)))
  exact contDiff_const.clm_comp ((S.contDiff_volterraInverse_coefficient t).clm_comp contDiff_const)

/-- Analytic formulation used when composing with the complex Fourier parameter. -/
theorem analyticAt_boundedPerturbation_coefficient (S : C0Semigroup ℂ E)
    (t : NNReal) (B : E →L[ℂ] E) :
    AnalyticAt ℂ (fun C : E →L[ℂ] E ↦ S.boundedPerturbation C t) B :=
  (S.contDiff_boundedPerturbation_coefficient t).contDiffAt.analyticAt

end

end C0Semigroup
