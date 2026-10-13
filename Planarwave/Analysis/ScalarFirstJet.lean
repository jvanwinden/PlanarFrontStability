/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCFirstJet
public import Planarwave.Analysis.BUCBilinear
public import Planarwave.Analysis.BUCNonlinear

@[expose] public section

/-!
# Product rule for scalar first jets

Multiplication of a value/derivative pair is a bounded bilinear operation
and preserves the closed subspace of genuine spatial derivative jets.
-/

namespace Planarwave

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiplication by a fixed scalar jet, including the product rule. -/
def scalarFirstJetMulRight (p : FirstJet E ℝ) : FirstJet E ℝ →L[ℝ] FirstJet E ℝ :=
  (p.1 • ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)).prod
    (p.1 • ContinuousLinearMap.snd ℝ ℝ (E →L[ℝ] ℝ) +
      (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] ℝ)).smulRight p.2)

@[simp] theorem scalarFirstJetMulRight_apply (p q : FirstJet E ℝ) :
    scalarFirstJetMulRight p q = (p.1 * q.1, p.1 • q.2 + q.1 • p.2) := rfl

theorem norm_scalarFirstJetMulRight_apply_le (p q : FirstJet E ℝ) :
    ‖scalarFirstJetMulRight p q‖ ≤ (2 * ‖p‖) * ‖q‖ := by
  rw [scalarFirstJetMulRight_apply, Prod.norm_def, max_le_iff]
  have hfst : ‖p.1‖ * ‖q.1‖ ≤ ‖p‖ * ‖q‖ :=
    mul_le_mul (norm_fst_le p) (norm_fst_le q) (norm_nonneg _) (norm_nonneg _)
  have hleft : ‖p.1‖ * ‖q.2‖ ≤ ‖p‖ * ‖q‖ :=
    mul_le_mul (norm_fst_le p) (norm_snd_le q) (norm_nonneg _) (norm_nonneg _)
  have hright : ‖q.1‖ * ‖p.2‖ ≤ ‖p‖ * ‖q‖ := by
    simpa [mul_comm] using
      mul_le_mul (norm_fst_le q) (norm_snd_le p) (norm_nonneg _) (norm_nonneg _)
  constructor
  · rw [norm_mul]
    nlinarith [mul_nonneg (norm_nonneg p) (norm_nonneg q)]
  · calc
      _ ≤ ‖p.1 • q.2‖ + ‖q.1 • p.2‖ := norm_add_le _ _
      _ = ‖p.1‖ * ‖q.2‖ + ‖q.1‖ * ‖p.2‖ := by rw [norm_smul, norm_smul]
      _ ≤ _ := by linarith

/-- The bounded bilinear multiplication law on scalar first jets. -/
def scalarFirstJetMul : FirstJet E ℝ →L[ℝ] FirstJet E ℝ →L[ℝ] FirstJet E ℝ :=
  LinearMap.mkContinuous
    { toFun := scalarFirstJetMulRight
      map_add' := by
        intro p q
        apply ContinuousLinearMap.ext
        intro r
        simp [scalarFirstJetMulRight_apply, add_mul, add_smul, smul_add]
        abel
      map_smul' := by
        intro c p
        apply ContinuousLinearMap.ext
        intro q
        simp [scalarFirstJetMulRight_apply, smul_add, smul_smul, mul_comm, mul_left_comm] }
    2 (fun p ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (norm_scalarFirstJetMulRight_apply_le p))

@[simp] theorem scalarFirstJetMul_apply (p q : FirstJet E ℝ) :
    scalarFirstJetMul p q = (p.1 * q.1, p.1 • q.2 + q.1 • p.2) := rfl

@[simp] theorem firstJetValue_mul (u v : BUC E (FirstJet E ℝ)) :
    firstJetValue (BUC.bilinearBUC scalarFirstJetMul u v) =
      BUC.smulBUC (firstJetValue u) (firstJetValue v) := by ext x; rfl

@[simp] theorem firstJetDerivative_mul (u v : BUC E (FirstJet E ℝ)) :
    firstJetDerivative (BUC.bilinearBUC scalarFirstJetMul u v) =
      BUC.smulBUC (firstJetValue u) (firstJetDerivative v) +
        BUC.smulBUC (firstJetValue v) (firstJetDerivative u) := by ext x; rfl

/-- The product of genuine derivative jets is again a genuine jet. -/
theorem scalarFirstJetMul_mem_submodule (u v : BUC E (FirstJet E ℝ))
    (hu : u ∈ firstJetSubmodule) (hv : v ∈ firstJetSubmodule) :
    BUC.bilinearBUC scalarFirstJetMul u v ∈ firstJetSubmodule := by
  intro x
  simpa only [firstJetValue_mul, firstJetDerivative_mul, BUC.add_apply, BUC.smulBUC_apply] using!
    (hu x).mul (hv x)

end

end Planarwave
