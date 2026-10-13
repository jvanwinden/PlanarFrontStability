/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCFirstJet
public import Planarwave.Analysis.BUCNonlinear

@[expose] public section

/-!
# Scalar multiplication of vector-valued first jets

The differentiated Cole--Hopf equation is vector-valued, but still has a
scalar multiplication coefficient. Its product rule is a bounded bilinear
operation on genuine value/derivative pairs.
-/

namespace Planarwave

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def firstJetSMulRight (p : FirstJet E ℝ) : FirstJet E F →L[ℝ] FirstJet E F :=
  (p.1 • ContinuousLinearMap.fst ℝ F (E →L[ℝ] F)).prod
    (p.1 • ContinuousLinearMap.snd ℝ F (E →L[ℝ] F) +
      ((ContinuousLinearMap.smulRightL ℝ E F) p.2).comp
        (ContinuousLinearMap.fst ℝ F (E →L[ℝ] F)))

@[simp] theorem firstJetSMulRight_apply (p : FirstJet E ℝ) (q : FirstJet E F) :
    firstJetSMulRight p q = (p.1 • q.1, p.1 • q.2 + p.2.smulRight q.1) := rfl

theorem norm_firstJetSMulRight_apply_le (p : FirstJet E ℝ) (q : FirstJet E F) :
    ‖firstJetSMulRight p q‖ ≤ (2 * ‖p‖) * ‖q‖ := by
  rw [firstJetSMulRight_apply, Prod.norm_def, max_le_iff]
  have h₁ := mul_le_mul (norm_fst_le p) (norm_fst_le q) (norm_nonneg _) (norm_nonneg _)
  have h₂ := mul_le_mul (norm_fst_le p) (norm_snd_le q) (norm_nonneg _) (norm_nonneg _)
  have h₃ := mul_le_mul (norm_snd_le p) (norm_fst_le q) (norm_nonneg _) (norm_nonneg _)
  constructor
  · rw [norm_smul]
    nlinarith [mul_nonneg (norm_nonneg p) (norm_nonneg q)]
  · calc
      _ ≤ ‖p.1 • q.2‖ + ‖p.2.smulRight q.1‖ := norm_add_le _ _
      _ = ‖p.1‖ * ‖q.2‖ + ‖p.2‖ * ‖q.1‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ _ := by linarith

/-- The value and derivative of a scalar-times-vector product. -/
def firstJetSMul : FirstJet E ℝ →L[ℝ] FirstJet E F →L[ℝ] FirstJet E F :=
  LinearMap.mkContinuous
    { toFun := firstJetSMulRight (E := E) (F := F)
      map_add' := by
        intro p q
        apply ContinuousLinearMap.ext
        intro r
        apply Prod.ext
        · simp [firstJetSMulRight_apply, add_smul]
        · ext v
          simp [firstJetSMulRight_apply, add_smul]
          abel
      map_smul' := by
        intro c p
        apply ContinuousLinearMap.ext
        intro q
        apply Prod.ext
        · simp [firstJetSMulRight_apply, smul_smul]
        · ext v
          simp [firstJetSMulRight_apply, smul_add, smul_smul] }
    2 (fun p ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (norm_firstJetSMulRight_apply_le p))

@[simp] theorem firstJetSMul_apply (p : FirstJet E ℝ) (q : FirstJet E F) :
    firstJetSMul p q = (p.1 • q.1, p.1 • q.2 + p.2.smulRight q.1) := rfl

@[simp] theorem firstJetValue_smul (g : BUC E (FirstJet E ℝ)) (u : BUC E (FirstJet E F)) :
    firstJetValue (BUC.bilinearBUC firstJetSMul g u) =
      BUC.smulBUC (firstJetValue g) (firstJetValue u) := by ext x; rfl

@[simp] theorem firstJetDerivative_smul (g : BUC E (FirstJet E ℝ)) (u : BUC E (FirstJet E F)) :
    firstJetDerivative (BUC.bilinearBUC firstJetSMul g u) =
      BUC.smulBUC (firstJetValue g) (firstJetDerivative u) +
        BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E F)
          (firstJetDerivative g) (firstJetValue u) := by ext x; rfl

theorem firstJetSMul_mem_submodule (g : BUC E (FirstJet E ℝ)) (u : BUC E (FirstJet E F))
    (hg : g ∈ firstJetSubmodule) (hu : u ∈ firstJetSubmodule) :
    BUC.bilinearBUC (firstJetSMul (E := E) (F := F)) g u ∈ firstJetSubmodule := by
  intro x
  simpa only [firstJetValue_smul, firstJetDerivative_smul, BUC.add_apply,
    BUC.smulBUC_apply, BUC.bilinearBUC_apply, ContinuousLinearMap.smulRightL_apply_apply] using!
    (hg x).smul (hu x)

end

end Planarwave
