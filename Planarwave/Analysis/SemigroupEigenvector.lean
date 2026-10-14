/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Semigroup evolution on an eigenspace

A generator eigenvector evolves by the scalar exponential. This supplies the critical-mode
identity used at the start of the Taylor estimate in Lemma 2.3 of the paper.
-/

open MeasureTheory Set

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A generator eigenvector evolves by the exponential of its eigenvalue. -/
theorem HasGeneratorAt.apply_eq_exp_smul {S : C0Semigroup ℂ E} {x : E} {z : ℂ}
    (h : S.HasGeneratorAt x (z • x)) (t : NNReal) :
    S t x = Complex.exp ((t : ℂ) * z) • x := by
  let F : ℝ → E := fun r ↦ Complex.exp (-(r : ℂ) * z) • S.realOrbit x r
  have hc : Continuous F := by
    apply Continuous.smul _ (S.continuous_realOrbit x)
    fun_prop
  have hd (r : ℝ) (hr : 0 ≤ r) : HasDerivWithinAt F 0 (Ioi r) r := by
    have he := (((hasDerivAt_id (r : ℂ)).neg.mul_const z).cexp).comp_ofReal
    have hs := h.hasDerivWithinAt hr
    have he' : HasDerivWithinAt (fun a : ℝ ↦ Complex.exp (-(a : ℂ) * z))
        (Complex.exp (-(r : ℂ) * z) * (-z)) (Ici r) r := by
      simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul] using! he.hasDerivWithinAt (s := Ici r)
    have hp := he'.smul hs
    have hz : Complex.exp (-(r : ℂ) * z) • S.realOrbit (z • x) r +
        (Complex.exp (-(r : ℂ) * z) * -z) • S.realOrbit x r = 0 := by
      simp only [realOrbit, map_smul, ← mul_smul, ← add_smul]
      ring_nf
      simp
    rw [hz] at hp
    exact hp.Ioi_of_Ici
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.2 hc.continuousOn
    (fun r hr ↦ hd r hr.1.le) (intervalIntegrable_const (c := (0 : E)))
  have hF : Complex.exp (-(t : ℂ) * z) • S t x = x := by
    have hi' : F t - F 0 = 0 := by simpa only [intervalIntegral.integral_zero] using! hi.symm
    simpa [F] using sub_eq_zero.mp hi'
  have heq := congrArg (fun y : E ↦ Complex.exp ((t : ℂ) * z) • y) hF
  simpa only [smul_smul, ← Complex.exp_add, neg_mul, add_neg_cancel,
    Complex.exp_zero, one_smul] using heq

/-- A bounded map with range in a generator eigenspace evolves by a scalar exponential. -/
theorem comp_eq_exp_smul_of_generator_eigenrange (S : C0Semigroup ℂ E)
    (P : E →L[ℂ] E) (z : ℂ) (hP : ∀ x, S.HasGeneratorAt (P x) (z • P x))
    (t : NNReal) : (S t).comp P = Complex.exp ((t : ℂ) * z) • P := by
  ext x
  exact (hP x).apply_eq_exp_smul t

end

end C0Semigroup
