/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCBilinear
public import Planarwave.Analysis.ComplexBUC2

@[expose] public section

/-!
# The common-domain longitudinal Fourier family

This is the operator family from Section 2 of the paper.  With a BUC coefficient family `A(z)` and
complexified diffusion `D`, it acts on the graph domain `BUC²` by

`L(q)v = D(v'' - q v) + c v' + A(z)v`.

The parameter dependence is exactly affine: `L(q) = L(0) - q D`.  This is the starting point for
the simple-eigenvalue perturbation argument in Proposition 2.1.
-/

open Function

universe u

noncomputable section

namespace Planarwave

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [SMulCommClass ℝ ℂ V] [CompleteSpace V]

abbrev LongitudinalSpace (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] [CompleteSpace V] := BUC ℝ V

abbrev LongitudinalDomain (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] [CompleteSpace V] := ComplexBUC2 V

/-- Apply a fixed endomorphism after the second derivative. -/
def diffusionSecondDerivative (D : V →L[ℂ] V) :
    LongitudinalDomain V →L[ℂ] LongitudinalSpace V :=
  (BUC.postcompCLM D).comp (ComplexBUC2.deriv2CLM V)

/-- Apply a fixed endomorphism to the underlying function. -/
def diffusionValue (D : V →L[ℂ] V) :
    LongitudinalDomain V →L[ℂ] LongitudinalSpace V :=
  (BUC.postcompCLM D).comp (ComplexBUC2.valueCLM V)

/-- Pointwise application of the variable coefficient family. -/
def coefficientTerm (A : BUC ℝ (V →L[ℂ] V)) :
    LongitudinalDomain V →L[ℂ] LongitudinalSpace V :=
  (BUC.operatorApplyCLM A).comp (ComplexBUC2.valueCLM V)

/-- The longitudinal common-domain family `L(q)`. -/
def longitudinalOperator (D : V →L[ℂ] V) (c q : ℂ)
    (A : BUC ℝ (V →L[ℂ] V)) :
    LongitudinalDomain V →L[ℂ] LongitudinalSpace V :=
  diffusionSecondDerivative D - q • diffusionValue D +
    c • ComplexBUC2.derivCLM V + coefficientTerm A

@[simp]
theorem diffusionSecondDerivative_apply (D : V →L[ℂ] V) (v : LongitudinalDomain V) (z : ℝ) :
    diffusionSecondDerivative D v z = D (ComplexBUC2.deriv2 V v z) := rfl

@[simp]
theorem diffusionValue_apply (D : V →L[ℂ] V) (v : LongitudinalDomain V) (z : ℝ) :
    diffusionValue D v z = D (v z) := rfl

@[simp]
theorem coefficientTerm_apply (A : BUC ℝ (V →L[ℂ] V))
    (v : LongitudinalDomain V) (z : ℝ) : coefficientTerm A v z = A z (v z) := rfl

@[simp]
theorem longitudinalOperator_apply (D : V →L[ℂ] V) (c q : ℂ)
    (A : BUC ℝ (V →L[ℂ] V)) (v : LongitudinalDomain V) (z : ℝ) :
    longitudinalOperator D c q A v z =
      D (ComplexBUC2.deriv2 V v z) - q • D (v z) +
        c • ComplexBUC2.deriv V v z + A z (v z) := by
  rfl

/-- Exact affine parameter dependence of the Fourier family. -/
theorem longitudinalOperator_eq_zero_sub (D : V →L[ℂ] V) (c q : ℂ)
    (A : BUC ℝ (V →L[ℂ] V)) :
    longitudinalOperator D c q A =
      longitudinalOperator D c 0 A - q • diffusionValue D := by
  simp [longitudinalOperator]
  module

/-- Difference of two members of the family. -/
theorem longitudinalOperator_sub (D : V →L[ℂ] V) (c q r : ℂ)
    (A : BUC ℝ (V →L[ℂ] V)) :
    longitudinalOperator D c q A - longitudinalOperator D c r A =
      (r - q) • diffusionValue D := by
  simp [longitudinalOperator]
  module

/-- Lipschitz dependence on the transverse Fourier parameter in operator norm. -/
theorem norm_longitudinalOperator_sub_le (D : V →L[ℂ] V) (c q r : ℂ)
    (A : BUC ℝ (V →L[ℂ] V)) :
    ‖longitudinalOperator D c q A - longitudinalOperator D c r A‖ ≤
      ‖r - q‖ * ‖diffusionValue D‖ := by
  rw [longitudinalOperator_sub]
  exact ContinuousLinearMap.opNorm_smul_le (r - q)
    (diffusionValue D : LongitudinalDomain V →L[ℂ] LongitudinalSpace V)

/-- The real transverse wavenumber `k` enters through `q = k²`. -/
def transverseFourierOperator (D : V →L[ℂ] V) (c : ℂ)
    (A : BUC ℝ (V →L[ℂ] V)) (k : ℝ) :
    LongitudinalDomain V →L[ℂ] LongitudinalSpace V :=
  longitudinalOperator D c (k ^ 2) A

@[simp]
theorem transverseFourierOperator_apply (D : V →L[ℂ] V) (c : ℂ)
    (A : BUC ℝ (V →L[ℂ] V)) (k : ℝ) (v : LongitudinalDomain V) (z : ℝ) :
    transverseFourierOperator D c A k v z =
      D (ComplexBUC2.deriv2 V v z) - (k ^ 2 : ℂ) • D (v z) +
        c • ComplexBUC2.deriv V v z + A z (v z) := by
  rfl

end Planarwave
