/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialComposition
public import Planarwave.Analysis.InverseModulationCoordinates
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-!
# Higher spatial bounds under inverse modulation

The coordinate shear has derivative `I + (0, Dσ ∘ fst)`. Its higher
derivatives therefore depend only on those of σ, not on the translation
`a = c*t`. The spatial chain rule transfers the `C^9` bound from the
reaction--diffusion solution to the perturbation, as in Step 4 of `lem:key`.
The cutoff version does not require smooth initial data: it differentiates
the already cut off solution and is valid also when the cutoff vanishes.
-/

namespace Planarwave

noncomputable section

universe u

variable {Y : Type} {F : Type u}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance modulationHigherScalarDualGroup : NormedAddCommGroup (Y →L[ℝ] ℝ) := inferInstance
local instance modulationHigherScalarDualSpace : NormedSpace ℝ (Y →L[ℝ] ℝ) := inferInstance
local instance modulationHigherShearOperatorGroup :
    NormedAddCommGroup ((Y × ℝ) →L[ℝ] (Y × ℝ)) := inferInstance
local instance modulationHigherShearOperatorSpace :
    NormedSpace ℝ ((Y × ℝ) →L[ℝ] (Y × ℝ)) := inferInstance

/-- Insert a transverse phase derivative into the longitudinal shear. -/
def modulationDerivativeLift : (Y →L[ℝ] ℝ) →L[ℝ] ((Y × ℝ) →L[ℝ] (Y × ℝ)) :=
  (ContinuousLinearMap.compL ℝ (Y × ℝ) ℝ (Y × ℝ) (ContinuousLinearMap.inr ℝ Y ℝ)).comp
    ((ContinuousLinearMap.compL ℝ (Y × ℝ) Y ℝ).flip (ContinuousLinearMap.fst ℝ Y ℝ))

@[simp]
theorem modulationDerivativeLift_apply (q : Y →L[ℝ] ℝ) (x : Y × ℝ) :
    modulationDerivativeLift q x = (0, q x.1) := rfl

theorem norm_modulationDerivativeLift_le : ‖modulationDerivativeLift (Y := Y)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg q)
  intro x
  simpa only [modulationDerivativeLift_apply, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)] using
    (q.le_opNorm x.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le x) (norm_nonneg q))

/-- The actual derivative of the spatial modulation map, as a BUC field. -/
def modulationDerivativeBUC (q : BUC Y (Y →L[ℝ] ℝ)) : BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ)) :=
  BUC.const (Y × ℝ) (ContinuousLinearMap.id ℝ (Y × ℝ)) +
    BUC.postcompCLM modulationDerivativeLift (q.comp Prod.fst uniformContinuous_fst)

@[simp]
theorem modulationDerivativeBUC_apply (q : BUC Y (Y →L[ℝ] ℝ)) (x v : Y × ℝ) :
    modulationDerivativeBUC q x v = v + (0, q x.1 v.1) := rfl

/-- The shear derivative formula is independent of the translation. -/
theorem hasFDerivAt_modulationCoordinates (a : ℝ) (σ : BUC Y ℝ)
    (q : BUC Y (Y →L[ℝ] ℝ)) (hd : ∀ y, HasFDerivAt σ (q y) y) (x : Y × ℝ) :
    HasFDerivAt (modulationCoordinates a σ) (modulationDerivativeBUC q x) x := by
  have h := ((hasFDerivAt_id x).add_const ((0 : Y), a)).add
    ((ContinuousLinearMap.inr ℝ Y ℝ).hasFDerivAt.comp x
      ((hd x.1).comp x (ContinuousLinearMap.fst ℝ Y ℝ).hasFDerivAt))
  convert! h using 1
  ext y <;> simp [modulationCoordinates]

/-- Common derivative bounds for the shear derivative. -/
theorem bucSpatialBound_modulationDerivative {k : ℕ} {q : BUC Y (Y →L[ℝ] ℝ)} {B : ℝ}
    (hq : BUCSpatialBound k q B) : BUCSpatialBound k (modulationDerivativeBUC q) (1 + B) := by
  have hc := (BUCSpatialBound.const (E := Y × ℝ) k (ContinuousLinearMap.id ℝ (Y × ℝ))).mono
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Y × ℝ))
  have hp := hq.precomp_contraction (ContinuousLinearMap.fst ℝ Y ℝ)
    (ContinuousLinearMap.norm_fst_le ℝ Y ℝ)
  have hl := (hp.postcomp modulationDerivativeLift).mono
    (show ‖modulationDerivativeLift (Y := Y)‖ * B ≤ B by
      have h := mul_le_mul_of_nonneg_right (norm_modulationDerivativeLift_le (Y := Y)) hq.nonneg
      simpa only [one_mul] using h)
  exact hc.add hl

/-- Finite-order bounds transfer through the actual inverse-modulation shear.
The constant depends on the phase derivative bound, not on `a = c*t`. -/
theorem BUCSpatialBound.modulationShift {k : ℕ} {u : BUC (Y × ℝ) F} {σ : BUC Y ℝ} {A B : ℝ}
    (hu : BUCSpatialBound k u A) (hσ : BUCSpatialBound k σ B) (a : ℝ) :
    BUCSpatialBound k (Planarwave.modulationShift a σ u)
      (bucSpatialCompositionConstant (1 + B) k * A) := by
  cases k with
  | zero =>
    change ‖Planarwave.modulationShift a σ u‖ ≤ 1 * A
    simpa only [norm_modulationShift, one_mul] using hu.norm_le
  | succ k =>
    obtain ⟨_, q, hq, hd⟩ := hσ
    exact hu.comp (modulationCoordinates a σ) (uniformContinuous_modulationCoordinates a σ)
      (modulationDerivativeBUC q) (hasFDerivAt_modulationCoordinates a σ q hd)
      (bucSpatialBound_modulationDerivative hq)

/-- Transfer the high-order bound to the inverse-modulated perturbation. -/
theorem BUCSpatialBound.modulationShift_sub {k : ℕ} {u p : BUC (Y × ℝ) F}
    {σ : BUC Y ℝ} {A B P : ℝ} (hu : BUCSpatialBound k u A)
    (hσ : BUCSpatialBound k σ B) (hp : BUCSpatialBound k p P) (a : ℝ) :
    BUCSpatialBound k (Planarwave.modulationShift a σ u - p)
      (bucSpatialCompositionConstant (1 + B) k * A + P) := by
  simpa only [sub_eq_add_neg] using (hu.modulationShift hσ a).add hp.neg

/-- The Step 4 transfer with the temporal cutoff, including the case `χ = 0`.
No high spatial regularity of the uncut initial datum is assumed. -/
theorem BUCSpatialBound.modulationShift_sub_cutoff {k : ℕ} {u p : BUC (Y × ℝ) F}
    {σ : BUC Y ℝ} {χ A B P : ℝ} (hu : BUCSpatialBound k (χ • u) A)
    (hσ : BUCSpatialBound k σ B) (hp : BUCSpatialBound k p P)
    (hχ : |χ| ≤ 1) (a : ℝ) :
    BUCSpatialBound k (χ • (Planarwave.modulationShift a σ u - p))
      (bucSpatialCompositionConstant (1 + B) k * A + P) := by
  have hcp := (hp.smul χ).mono
    (show |χ| * P ≤ P by nlinarith [hp.nonneg])
  have h := hu.modulationShift_sub hσ hcp a
  have heq : Planarwave.modulationShift a σ (χ • u) - χ • p =
      χ • (Planarwave.modulationShift a σ u - p) := by
    ext x
    simp only [modulationShift_apply, BUC.sub_apply, BUC.smul_apply, smul_sub]
  rwa [heq] at h

end

end Planarwave
