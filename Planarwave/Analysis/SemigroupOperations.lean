/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Planarwave.Analysis.Semigroup
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section

/-!
# Operations on strongly continuous semigroups

This file provides the two constructions used in the diagonal-diffusion step of Lemma 2.2:
multiplication by a real exponential and finite coordinatewise products.
-/

open scoped NNReal

noncomputable section

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

section Conjugate

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Transport a strongly continuous semigroup through a continuous linear equivalence.  This is
the abstract conjugation step used when the paper returns from diffusion eigenvector coordinates
to the original state space. -/
def conjugate (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F) : C0Semigroup ℂ F where
  toFun t := (e : E →L[ℂ] F).comp ((S t).comp (e.symm : F →L[ℂ] E))
  map_zero' := by
    ext x
    change e (S 0 (e.symm x)) = x
    simp
  map_add' s t := by
    ext x
    change e (S (s + t) (e.symm x)) =
      e (S s (e.symm (e (S t (e.symm x)))))
    rw [S.add_apply]
    simp
  strongContinuous' x := by
    change Continuous fun t : NNReal ↦ e (S t (e.symm x))
    exact e.continuous.comp (S.strongContinuous (e.symm x))

@[simp]
theorem conjugate_apply (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F)
    (t : NNReal) (x : F) :
    S.conjugate e t x = e (S t (e.symm x)) := rfl

/-- Conjugation costs at most the condition number of the change of coordinates. -/
theorem norm_conjugate_le (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F) (t : NNReal) :
    ‖S.conjugate e t‖ ≤ ‖(e : E →L[ℂ] F)‖ * ‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖ := by
  calc
    ‖S.conjugate e t‖ ≤
        ‖(e : E →L[ℂ] F)‖ * ‖(S t).comp (e.symm : F →L[ℂ] E)‖ :=
      (e : E →L[ℂ] F).opNorm_comp_le _
    _ ≤ ‖(e : E →L[ℂ] F)‖ *
        (‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖) := by
      gcongr
      exact (S t).opNorm_comp_le (e.symm : F →L[ℂ] E)
    _ = ‖(e : E →L[ℂ] F)‖ * ‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖ := by
      rw [mul_assoc]

/-- A scalar bound on a semigroup is preserved under conjugation up to the condition number. -/
theorem norm_conjugate_le_of_norm_le (S : C0Semigroup ℂ E) (e : E ≃L[ℂ] F)
    (t : NNReal) {M : ℝ} (hS : ‖S t‖ ≤ M) :
    ‖S.conjugate e t‖ ≤
      (‖(e : E →L[ℂ] F)‖ * ‖(e.symm : F →L[ℂ] E)‖) * M := by
  calc
    ‖S.conjugate e t‖ ≤
        ‖(e : E →L[ℂ] F)‖ * ‖S t‖ * ‖(e.symm : F →L[ℂ] E)‖ :=
      S.norm_conjugate_le e t
    _ ≤ ‖(e : E →L[ℂ] F)‖ * M * ‖(e.symm : F →L[ℂ] E)‖ := by
      gcongr
    _ = (‖(e : E →L[ℂ] F)‖ * ‖(e.symm : F →L[ℂ] E)‖) * M := by
      ring

end Conjugate

/-- Multiply a complex-linear semigroup by the scalar exponential `exp (ω t)`. -/
def rescaleRealExp (S : C0Semigroup ℂ E) (ω : ℝ) : C0Semigroup ℂ E where
  toFun t := (Real.exp (ω * (t : ℝ)) : ℂ) • S t
  map_zero' := by
    change (Real.exp (ω * (0 : ℝ)) : ℂ) • S 0 = ContinuousLinearMap.id ℂ E
    simp [S.map_zero]
  map_add' s t := by
    ext x
    change (Real.exp (ω * ((s + t : NNReal) : ℝ)) : ℂ) • S (s + t) x =
      (Real.exp (ω * (s : ℝ)) : ℂ) •
        S s ((Real.exp (ω * (t : ℝ)) : ℂ) • S t x)
    rw [S.add_apply]
    simp [NNReal.coe_add, mul_add, Real.exp_add, smul_smul]
  strongContinuous' x := by
    have hS : Continuous fun t : NNReal ↦ S t x := S.strongContinuous x
    have hexp : Continuous fun t : NNReal ↦ (Real.exp (ω * (t : ℝ)) : ℂ) := by
      fun_prop
    change Continuous fun t : NNReal ↦ (Real.exp (ω * (t : ℝ)) : ℂ) • S t x
    exact hexp.smul hS

@[simp]
theorem rescaleRealExp_apply (S : C0Semigroup ℂ E) (ω : ℝ) (t : NNReal) (x : E) :
    S.rescaleRealExp ω t x = (Real.exp (ω * (t : ℝ)) : ℂ) • S t x := rfl

/-- Operator-norm estimate for exponential rescaling. -/
theorem norm_rescaleRealExp_le (S : C0Semigroup ℂ E) (ω : ℝ) (t : NNReal) :
    ‖S.rescaleRealExp ω t‖ ≤ Real.exp (ω * (t : ℝ)) * ‖S t‖ := by
  calc
    ‖S.rescaleRealExp ω t‖ ≤
        ‖(Real.exp (ω * (t : ℝ)) : ℂ)‖ * ‖S t‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = Real.exp (ω * (t : ℝ)) * ‖S t‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- A contraction remains bounded by its scalar exponential after rescaling. -/
theorem norm_rescaleRealExp_of_isContraction_le
    (S : C0Semigroup ℂ E) (hS : S.IsContraction) (ω : ℝ) (t : NNReal) :
    ‖S.rescaleRealExp ω t‖ ≤ Real.exp (ω * (t : ℝ)) := by
  calc
    ‖S.rescaleRealExp ω t‖ ≤ Real.exp (ω * (t : ℝ)) * ‖S t‖ :=
      S.norm_rescaleRealExp_le ω t
    _ ≤ Real.exp (ω * (t : ℝ)) * 1 := by
      gcongr
      exact hS t
    _ = Real.exp (ω * (t : ℝ)) := mul_one _

section Pi

variable {ι : Type*} [Fintype ι]
  {X : ι → Type*}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
  [∀ i, CompleteSpace (X i)]

/-- Finite coordinatewise product of strongly continuous semigroups. -/
def pi (S : ∀ i, C0Semigroup ℂ (X i)) : C0Semigroup ℂ (∀ i, X i) where
  toFun t := ContinuousLinearMap.piMap fun i ↦ S i t
  map_zero' := by
    ext x i
    exact (S i).zero_apply (x i)
  map_add' s t := by
    ext x i
    exact (S i).add_apply s t (x i)
  strongContinuous' x := by
    exact continuous_pi fun i ↦ (S i).strongContinuous (x i)

@[simp]
theorem pi_apply (S : ∀ i, C0Semigroup ℂ (X i)) (t : NNReal) (x : ∀ i, X i)
    (i : ι) : pi S t x i = S i t (x i) := rfl

/-- A common coordinatewise operator-norm bound also bounds the finite product semigroup. -/
theorem norm_pi_le (S : ∀ i, C0Semigroup ℂ (X i)) (t : NNReal)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, ‖S i t‖ ≤ M) :
    ‖pi S t‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg x))).2
  intro i
  calc
    ‖S i t (x i)‖ ≤ ‖S i t‖ * ‖x i‖ := (S i t).le_opNorm (x i)
    _ ≤ M * ‖x‖ := by
      exact mul_le_mul (h i) (norm_le_pi_norm x i) (norm_nonneg _) hM

end Pi

end C0Semigroup

end
