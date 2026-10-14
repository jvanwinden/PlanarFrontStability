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
# Complex exponential rescaling of a semigroup

Multiplication by `exp (t z)` shifts the full generator by `z I`, without changing its domain.
This is used to construct the Laplace resolvent from an exponentially decaying semigroup.
-/

open Set

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Complex exponential rescaling of a strongly continuous semigroup. -/
def rescaleExp (S : C0Semigroup ℂ E) (z : ℂ) : C0Semigroup ℂ E where
  toFun t := Complex.exp ((t : ℂ) * z) • S t
  map_zero' := by simp
  map_add' s t := by
    ext x
    change Complex.exp (((s + t : NNReal) : ℂ) * z) • S (s + t) x =
      Complex.exp ((s : ℂ) * z) • S s (Complex.exp ((t : ℂ) * z) • S t x)
    rw [S.add_apply]
    simp [NNReal.coe_add, Complex.ofReal_add, add_mul, Complex.exp_add, smul_smul]
  strongContinuous' x := by
    change Continuous fun t : NNReal ↦ Complex.exp ((t : ℂ) * z) • S t x
    exact (by fun_prop : Continuous fun t : NNReal ↦ Complex.exp ((t : ℂ) * z)).smul
      (S.strongContinuous x)

@[simp]
theorem rescaleExp_apply (S : C0Semigroup ℂ E) (z : ℂ) (t : NNReal) (x : E) :
    S.rescaleExp z t x = Complex.exp ((t : ℂ) * z) • S t x := rfl

@[simp]
theorem rescaleExp_zero (S : C0Semigroup ℂ E) : S.rescaleExp 0 = S := by
  ext t x
  simp

theorem rescaleExp_add (S : C0Semigroup ℂ E) (z w : ℂ) :
    (S.rescaleExp z).rescaleExp w = S.rescaleExp (z + w) := by
  ext t x
  simp only [rescaleExp_apply, smul_smul, ← Complex.exp_add, mul_add]
  rw [add_comm]

/-- Exact change of the operator norm under complex rescaling. -/
theorem norm_rescaleExp (S : C0Semigroup ℂ E) (z : ℂ) (t : NNReal) :
    ‖S.rescaleExp z t‖ = Real.exp ((t : ℝ) * z.re) * ‖S t‖ := by
  change ‖Complex.exp ((t : ℂ) * z) • S t‖ = _
  rw [norm_smul, Complex.norm_exp]
  simp

/-- The rescaled generator acts by `A x + z x` on the original domain. -/
theorem HasGeneratorAt.rescaleExp {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) (z : ℂ) :
    (S.rescaleExp z).HasGeneratorAt x (y + z • x) := by
  have he : HasDerivAt (fun r : ℝ ↦ Complex.exp ((r : ℂ) * z)) z 0 := by
    simpa using! (((hasDerivAt_id (0 : ℂ)).mul_const z).cexp).comp_ofReal
  have hd : HasDerivWithinAt
      (fun r : ℝ ↦ Complex.exp ((r : ℂ) * z) • S.realOrbit x r)
      (y + z • x) (Ici 0) 0 := by
    simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, realOrbit_zero] using!
      he.hasDerivWithinAt.smul h
  apply hd.congr
  · intro r hr
    simp only [realOrbit, rescaleExp_apply, Real.coe_toNNReal _ hr]
  · simp [realOrbit]

/-- Complex rescaling shifts the full generator graph, with no extra domain assumption. -/
theorem rescaleExp_hasGeneratorAt_iff (S : C0Semigroup ℂ E) (z : ℂ) (x y : E) :
    (S.rescaleExp z).HasGeneratorAt x y ↔ S.HasGeneratorAt x (y - z • x) := by
  constructor
  · intro h
    have hd := h.rescaleExp (-z)
    simpa only [rescaleExp_add, add_neg_cancel, rescaleExp_zero, neg_smul, sub_eq_add_neg] using! hd
  · intro h
    simpa only [sub_add_cancel] using! h.rescaleExp z

end

end C0Semigroup
