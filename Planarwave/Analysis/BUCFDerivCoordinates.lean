/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCEquiv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-!
# BUC derivatives under finite coordinate changes

Assembling scalar derivative data and postcomposing by a fixed linear map
preserves bounded uniform continuity and the operator-norm bounds. Repeating
this construction handles the second spatial derivative of matrix heat flow.
-/

namespace BUC

noncomputable section

variable {E F G : Type*} {ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Assemble a finite family of derivatives and then change the value coordinates. -/
def fderivCoordinates (L : (ι → F) →L[ℝ] G) :
    (ι → E →L[ℝ] F) →L[ℝ] (E →L[ℝ] G) :=
  (L.postcomp E).comp (ContinuousLinearMap.piEquivL ℝ E (fun _ : ι ↦ F)).toContinuousLinearMap

omit [Fintype ι] in
@[simp]
theorem fderivCoordinates_apply (L : (ι → F) →L[ℝ] G) (g : ι → E →L[ℝ] F) (v : E) :
    fderivCoordinates L g v = L (fun i ↦ g i v) := rfl

/-- The derivative coordinate map costs at most the original change of coordinates. -/
theorem norm_fderivCoordinates_le (L : (ι → F) →L[ℝ] G) :
    ‖fderivCoordinates (E := E) L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro g
  change ‖L.comp (ContinuousLinearMap.pi g)‖ ≤ _
  exact (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_pi_le_of_le (fun i ↦ norm_le_pi_norm g i) (norm_nonneg g))
    (norm_nonneg L))

/-- The same coordinate assembly on BUC derivative fields. -/
def fderivPostcompPi (L : (ι → F) →L[ℝ] G) (g : ι → BUC E (E →L[ℝ] F)) :
    BUC E (E →L[ℝ] G) :=
  postcompCLM (fderivCoordinates L) (ofPi g)

@[simp]
theorem fderivPostcompPi_apply (L : (ι → F) →L[ℝ] G)
    (g : ι → BUC E (E →L[ℝ] F)) (x v : E) :
    fderivPostcompPi L g x v = L (fun i ↦ g i x v) := rfl

/-- Uniform derivative bounds survive finite coordinate changes. -/
theorem norm_fderivPostcompPi_le (L : (ι → F) →L[ℝ] G)
    (g : ι → BUC E (E →L[ℝ] F)) :
    ‖fderivPostcompPi L g‖ ≤ ‖L‖ * ‖g‖ := by
  have hg : ‖ofPi g‖ ≤ ‖g‖ := by
    apply (BUC.norm_le (norm_nonneg g)).mpr
    intro x
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg g)).mpr
    intro i
    exact ((g i).norm_apply_le x).trans (norm_le_pi_norm g i)
  exact (norm_postcompCLM_apply_le (fderivCoordinates L) (ofPi g)).trans
    (mul_le_mul (norm_fderivCoordinates_le L) hg (norm_nonneg _) (norm_nonneg L))

/-- Chain rule for the BUC derivative coordinate assembly. -/
theorem hasFDerivAt_postcomp_ofPi (L : (ι → F) →L[ℝ] G)
    (f : ι → BUC E F) (g : ι → BUC E (E →L[ℝ] F))
    (hg : ∀ i x, HasFDerivAt (f i) (g i x) x) (x : E) :
    HasFDerivAt (postcompCLM L (ofPi f)) (fderivPostcompPi L g x) x := by
  exact L.hasFDerivAt.comp x (hasFDerivAt_pi.mpr (fun i ↦ hg i x))

end

end BUC
