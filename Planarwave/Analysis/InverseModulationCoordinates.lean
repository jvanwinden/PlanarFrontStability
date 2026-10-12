/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC

@[expose] public section

/-!
# The inverse-modulation change of coordinates

The shear `(y,z) ↦ (y,z+a+σ(y))` preserves BUC and its supremum norm.
This proves the equality of the inverse- and forward-modulated perturbation
norms used at the beginning of Section 4 of the paper.
-/

namespace Planarwave

noncomputable section

variable {Y F : Type*} [NormedAddCommGroup Y] [NormedAddCommGroup F]

/-- The spatial modulation shear at a fixed time (`a = c*t`). -/
def modulationCoordinates (a : ℝ) (σ : BUC Y ℝ) (x : Y × ℝ) : Y × ℝ :=
  (x.1, x.2 + a + σ x.1)

theorem uniformContinuous_modulationCoordinates (a : ℝ) (σ : BUC Y ℝ) :
    UniformContinuous (modulationCoordinates a σ) :=
  uniformContinuous_fst.prodMk
    ((uniformContinuous_snd.add uniformContinuous_const).add
      (σ.uniformContinuous.comp uniformContinuous_fst))

/-- Negating the speed shift and phase gives the inverse shear. -/
@[simp]
theorem modulationCoordinates_inverse (a : ℝ) (σ : BUC Y ℝ) (x : Y × ℝ) :
    modulationCoordinates (-a) (-σ) (modulationCoordinates a σ x) = x := by
  ext
  · rfl
  · simp only [modulationCoordinates, BUC.neg_apply]
    ring

/-- Pull back BUC data by the inverse-modulation coordinates. -/
def modulationShift (a : ℝ) (σ : BUC Y ℝ) (v : BUC (Y × ℝ) F) : BUC (Y × ℝ) F :=
  v.comp (modulationCoordinates a σ) (uniformContinuous_modulationCoordinates a σ)

@[simp]
theorem modulationShift_apply (a : ℝ) (σ : BUC Y ℝ) (v : BUC (Y × ℝ) F) (x : Y × ℝ) :
    modulationShift a σ v x = v (x.1, x.2 + a + σ x.1) := rfl

@[simp]
theorem modulationShift_inverse (a : ℝ) (σ : BUC Y ℝ) (v : BUC (Y × ℝ) F) :
    modulationShift (-a) (-σ) (modulationShift a σ v) = v := by
  ext x
  change v (modulationCoordinates a σ (modulationCoordinates (-a) (-σ) x)) = v x
  have h := modulationCoordinates_inverse (-a) (-σ) x
  simpa only [neg_neg] using congrArg v h

/-- The modulation change of variables preserves the exact spatial supremum norm. -/
theorem norm_modulationShift (a : ℝ) (σ : BUC Y ℝ) (v : BUC (Y × ℝ) F) :
    ‖modulationShift a σ v‖ = ‖v‖ := by
  apply le_antisymm (BUC.norm_comp_le _ _ _)
  calc
    ‖v‖ = ‖modulationShift (-a) (-σ) (modulationShift a σ v)‖ := by rw [modulationShift_inverse]
    _ ≤ ‖modulationShift a σ v‖ := BUC.norm_comp_le _ _ _

@[simp]
theorem modulationShift_sub (a : ℝ) (σ : BUC Y ℝ) (u v : BUC (Y × ℝ) F) :
    modulationShift a σ (u - v) = modulationShift a σ u - modulationShift a σ v := by
  ext x
  rfl

/-- The inverse-modulated residual is the pullback of the forward-modulated residual. -/
theorem inverseModulatedPerturbation_eq_shift (a : ℝ) (σ : BUC Y ℝ)
    (u p : BUC (Y × ℝ) F) :
    modulationShift a σ u - p = modulationShift a σ (u - modulationShift (-a) (-σ) p) := by
  rw [modulationShift_sub]
  have h := modulationShift_inverse (-a) (-σ) p
  simpa only [neg_neg] using congrArg (fun q ↦ modulationShift a σ u - q) h.symm

/-- Controlling the inverse modulation controls the physical forward residual
with precisely the same constant, as asserted in Section 4. -/
theorem norm_inverseModulatedPerturbation_eq_forward (a : ℝ) (σ : BUC Y ℝ)
    (u p : BUC (Y × ℝ) F) :
    ‖modulationShift a σ u - p‖ = ‖u - modulationShift (-a) (-σ) p‖ := by
  rw [inverseModulatedPerturbation_eq_shift, norm_modulationShift]

end

end Planarwave
