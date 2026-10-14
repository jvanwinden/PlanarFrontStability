/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupUniqueness

@[expose] public section

/-!
# Intertwining strongly continuous semigroups through their generators

A bounded map intertwining the generator relations also intertwines the semigroups. The proof
uses `T(t-r) B S(r)x` on the dense generator domain, just as the uniqueness proof. This allows
the critical spectral projection and its complement to be commuted through the front evolution.
-/

open MeasureTheory Set

namespace C0Semigroup

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A bounded generator intertwiner is a semigroup intertwiner. -/
theorem comp_eq_comp_of_generator_intertwining (S : C0Semigroup ℂ E) (T : C0Semigroup ℂ F)
    (B : E →L[ℂ] F)
    (hB : ∀ x y, S.HasGeneratorAt x y → T.HasGeneratorAt (B x) (B y)) (t : NNReal) :
    (T t).comp B = B.comp (S t) := by
  have honDomain {x y : E} (hx : S.HasGeneratorAt x y) : T t (B x) = B (S t x) := by
    let G : ℝ → F := fun r ↦ T.realOrbit (B (S.realOrbit x r)) ((t : ℝ) - r)
    have hc : Continuous G := T.continuous_realOrbit_joint.comp
      ((continuous_const.sub continuous_id).prodMk (B.continuous.comp (S.continuous_realOrbit x)))
    have hd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (t : ℝ)) : HasDerivAt G 0 r := by
      have hpair : T.HasGeneratorAt (B (S.realOrbit x r)) (B (S.realOrbit y r)) :=
        hB _ _ (hx.apply r.toNNReal)
      have hfixed := (hpair.hasDerivAt (sub_pos.mpr hr.2)).scomp_of_eq r
        ((hasDerivAt_id r).const_sub (t : ℝ)) (by rfl)
      have hu : HasDerivAt (fun s ↦ B (S.realOrbit x s)) (B (S.realOrbit y r)) r :=
        (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r (hx.hasDerivAt hr.1)
      have hd := T.hasDerivAt_realOrbit_apply
        (a := fun s : ℝ ↦ (t : ℝ) - s)
        (u := fun s ↦ B (S.realOrbit x s)) (by fun_prop) hu hfixed
      simpa only [neg_smul, one_smul, add_neg_cancel] using! hd
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.2 hc.continuousOn hd
      (intervalIntegrable_const (c := (0 : F)))
    have heq : G t = G 0 := sub_eq_zero.mp (by simpa only [intervalIntegral.integral_zero] using! hi.symm)
    simpa [G] using heq.symm
  have heq := Continuous.ext_on S.dense_generatorDomain
    ((T t).comp B).continuous (B.comp (S t)).continuous (by
      rintro x ⟨y, hy⟩
      exact honDomain hy)
  exact ContinuousLinearMap.ext (congrFun heq)

/-- A bounded map preserving the generator graph commutes with the semigroup. -/
theorem comp_comm_of_generator_comm (S : C0Semigroup ℂ E) (P : E →L[ℂ] E)
    (hP : ∀ x y, S.HasGeneratorAt x y → S.HasGeneratorAt (P x) (P y)) (t : NNReal) :
    (S t).comp P = P.comp (S t) :=
  S.comp_eq_comp_of_generator_intertwining S P hP t

end

end C0Semigroup
