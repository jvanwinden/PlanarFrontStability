/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCFDerivCoordinates
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# Longitudinal and mixed derivatives of spatial BUC data

Extract the derivative fields used in the inverse-modulated equation from two
successive BUC Fréchet derivatives in split coordinates `(y,z)`. Their norms
are controlled by the original first and second derivative norms.
-/

namespace BUC

noncomputable section

variable {Y F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : NormedAddCommGroup (BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := (Y × ℝ) →L[ℝ] F)
local instance : NormedAddCommGroup (BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := (Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)

/-- Apply a first derivative field to the unit longitudinal direction. -/
def longitudinalDerivativeField (g : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F)) : BUC (Y × ℝ) F :=
  postcompCLM (ContinuousLinearMap.apply ℝ F (0, 1)) g

@[simp]
theorem longitudinalDerivativeField_apply (g : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F)) (x : Y × ℝ) :
    longitudinalDerivativeField g x = g x (0, 1) := rfl

theorem norm_longitudinalDerivativeField_le (g : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F)) :
    ‖longitudinalDerivativeField g‖ ≤ ‖g‖ := by
  apply (BUC.norm_le (norm_nonneg g)).mpr
  intro x
  calc
    ‖g x (0, 1)‖ ≤ ‖g x‖ * ‖((0 : Y), (1 : ℝ))‖ := (g x).le_opNorm _
    _ = ‖g x‖ := by simp
    _ ≤ ‖g‖ := g.norm_apply_le x

/-- Apply a second derivative field twice in the longitudinal direction. -/
def longitudinalSecondDerivativeField
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) : BUC (Y × ℝ) F :=
  longitudinalDerivativeField (longitudinalDerivativeField (F := (Y × ℝ) →L[ℝ] F) h)

@[simp]
theorem longitudinalSecondDerivativeField_apply
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) (x : Y × ℝ) :
    longitudinalSecondDerivativeField h x = h x (0, 1) (0, 1) := rfl

theorem norm_longitudinalSecondDerivativeField_le
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) :
    ‖longitudinalSecondDerivativeField h‖ ≤ ‖h‖ :=
  (norm_longitudinalDerivativeField_le _).trans
    (norm_longitudinalDerivativeField_le (F := (Y × ℝ) →L[ℝ] F) h)

/-- The transverse derivative of the longitudinal derivative. -/
def mixedDerivativeField
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) : BUC (Y × ℝ) (Y →L[ℝ] F) :=
  postcompCLM (𝕜 := ℝ) (E := (Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F) (F := Y →L[ℝ] F)
    ((ContinuousLinearMap.precomp F (ContinuousLinearMap.inl ℝ Y ℝ)).comp
      ((ContinuousLinearMap.apply ℝ F ((0 : Y), (1 : ℝ))).postcomp (Y × ℝ))) h

@[simp]
theorem mixedDerivativeField_apply
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) (x : Y × ℝ) (y : Y) :
    mixedDerivativeField h x y = h x (y, 0) (0, 1) := rfl

theorem norm_mixedDerivativeField_le
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) :
    ‖mixedDerivativeField h‖ ≤ ‖h‖ := by
  apply (BUC.norm_le (norm_nonneg h)).mpr
  intro x
  have hhx : ‖h x‖ ≤ ‖h‖ :=
    @BUC.norm_apply_le (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F) inferInstance
      ContinuousLinearMap.toNormedAddCommGroup h x
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h)
  intro y
  calc
    ‖h x (y, 0) (0, 1)‖ ≤ ‖h x (y, 0)‖ * ‖((0 : Y), (1 : ℝ))‖ :=
      (h x (y, 0)).le_opNorm _
    _ = ‖h x (y, 0)‖ := by simp
    _ ≤ ‖h x‖ * ‖(y, (0 : ℝ))‖ := (h x).le_opNorm _
    _ ≤ ‖h‖ * ‖y‖ := by simpa using mul_le_mul_of_nonneg_right hhx (norm_nonneg y)

/-- The extracted first derivative is the derivative on each longitudinal slice. -/
theorem hasDerivAt_longitudinalDerivativeField (v : BUC (Y × ℝ) F)
    (g : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F))
    (hg : ∀ x, HasFDerivAt v (g x) x) (y : Y) (z : ℝ) :
    HasDerivAt (fun r ↦ v (y, r)) (longitudinalDerivativeField g (y, z)) z :=
  (hg (y, z)).comp_hasDerivAt z ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))

/-- Longitudinal second derivatives are extracted from the same Fréchet Hessian. -/
theorem hasDerivAt_longitudinalSecondDerivativeField
    (g : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F))
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F))
    (hh : ∀ x, HasFDerivAt g (h x) x) (y : Y) (z : ℝ) :
    HasDerivAt (fun r ↦ longitudinalDerivativeField g (y, r))
      (longitudinalSecondDerivativeField h (y, z)) z :=
  (ContinuousLinearMap.apply ℝ F ((0 : Y), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt z
    ((hh (y, z)).comp_hasDerivAt z ((hasDerivAt_const z y).prodMk (hasDerivAt_id z)))

/-- The mixed field really is `D_y ∂z v`, not an independent derivative datum. -/
theorem hasFDerivAt_mixedDerivativeField
    (g : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F))
    (h : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F))
    (hh : ∀ x, HasFDerivAt g (h x) x) (y : Y) (z : ℝ) :
    HasFDerivAt (fun r ↦ longitudinalDerivativeField g (r, z)) (mixedDerivativeField h (y, z)) y :=
  (ContinuousLinearMap.apply ℝ F ((0 : Y), (1 : ℝ))).hasFDerivAt.comp y
    ((hh (y, z)).comp y ((hasFDerivAt_id y).prodMk (hasFDerivAt_const z y)))

end

end BUC
