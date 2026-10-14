/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ColeHopfInverseDerivative
public import Planarwave.Analysis.ForcedColeHopfSecondDerivativeBounds

@[expose] public section

/-!
# Hessian and Laplacian bounds for the inverse Cole--Hopf transform

Differentiate the actual inverse slope and use the product rule. On the
small range the Hessian is bounded by `2 ‖D²ξ‖ + 4 |β| ‖Dξ‖²`.
Taking the trace gives a continuous BUC realization of the phase
Laplacian, which is needed by the paper's nonlinear estimates.
-/

open Set
open scoped Laplacian

namespace Planarwave

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the inverse Cole--Hopf slope, including `β = 0`. -/
theorem hasFDerivAt_coleHopfInv_slope {β : ℝ} {ξ : E → ℝ} {q : E →L[ℝ] ℝ} {x : E}
    (hd : HasFDerivAt ξ q x) (hx : |β * ξ x| ≤ 1 / 2) :
    HasFDerivAt (fun y ↦ (1 + β * ξ y)⁻¹)
      ((-β * ((1 + β * ξ x)⁻¹) ^ 2) • q) x := by
  have hn : 1 + β * ξ x ≠ 0 := by linarith [(abs_le.mp hx).1]
  have hlin : HasFDerivAt (fun y ↦ 1 + β * ξ y) (β • q) x :=
    (hd.const_smul β).const_add 1
  have heq : -((1 + β * ξ x) ^ 2)⁻¹ * β = -β * ((1 + β * ξ x)⁻¹) ^ 2 := by
    rw [inv_pow]
    ring
  simpa only [smul_smul, heq] using! (hasDerivAt_inv hn).comp_hasFDerivAt x hlin

local instance inverseC2FirstBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance inverseC2FirstBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance inverseC2TensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseC2TensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseC2SecondBUCNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
local instance inverseC2SecondBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance

/-- Genuine time-continuous BUC first and second derivatives of the inverse
phase, with explicit estimates in terms of the Cole--Hopf derivatives. -/
theorem exists_coleHopfInv_buc_second_fderivative {β T : ℝ} {ξ σ : ℝ → BUC E ℝ}
    (hξ : ContinuousOn ξ (Icc 0 T)) (q : ℝ → BUC E (E →L[ℝ] ℝ))
    (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ))
    (hqc : ContinuousOn q (Icc 0 T)) (hhc : ContinuousOn h (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x)
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hσ : ∀ t ∈ Icc 0 T, ∀ x, σ t x = coleHopfInv β (ξ t x)) :
    ∃ (Q : ℝ → BUC E (E →L[ℝ] ℝ)) (H : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      ContinuousOn Q (Icc 0 T) ∧ ContinuousOn H (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T,
        (∀ x, HasFDerivAt (σ t) (Q t x) x ∧ HasFDerivAt (Q t) (H t x) x) ∧
        ‖Q t‖ ≤ 2 * ‖q t‖ ∧ ‖H t‖ ≤ 2 * ‖h t‖ + (4 * |β|) * ‖q t‖ ^ 2 := by
  obtain ⟨S, hSc, hS⟩ := exists_continuous_coleHopfInvSlope_on ξ hξ hsmall
  let B₀ : BUC E ℝ →L[ℝ] BUC E ℝ →L[ℝ] BUC E ℝ :=
    BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)
  let B₁ : BUC E ℝ →L[ℝ] BUC E (E →L[ℝ] ℝ) →L[ℝ] BUC E (E →L[ℝ] ℝ) :=
    BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)
  let B₂ : BUC E ℝ →L[ℝ] BUC E (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
      BUC E (E →L[ℝ] E →L[ℝ] ℝ) := BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)
  let B₃ : BUC E (E →L[ℝ] ℝ) →L[ℝ] BUC E (E →L[ℝ] ℝ) →L[ℝ]
      BUC E (E →L[ℝ] E →L[ℝ] ℝ) :=
    BUC.bilinearBUCCLM (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ))
  let D := fun t ↦ (-β) • BUC.smulBUC (BUC.smulBUC (S t) (S t)) (q t)
  let Q := fun t ↦ BUC.smulBUC (S t) (q t)
  let H := fun t ↦ BUC.smulBUC (S t) (h t) +
    BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (D t) (q t)
  have hS2c : ContinuousOn (fun t ↦ BUC.smulBUC (S t) (S t)) (Icc 0 T) :=
    (B₀.continuous.comp_continuousOn hSc).clm_apply hSc
  have hDc : ContinuousOn D (Icc 0 T) :=
    ((B₁.continuous.comp_continuousOn hS2c).clm_apply hqc).const_smul (-β)
  refine ⟨Q, H, (B₁.continuous.comp_continuousOn hSc).clm_apply hqc,
    ((B₂.continuous.comp_continuousOn hSc).clm_apply hhc).add
      ((B₃.continuous.comp_continuousOn hDc).clm_apply hqc), ?_⟩
  intro t ht
  have hSd : ∀ x, HasFDerivAt (S t) (D t x) x := by
    intro x
    have hx : |β * ξ t x| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left ((ξ t).norm_apply_le x) (abs_nonneg β)).trans (hsmall t ht)
    have heq : (S t : E → ℝ) = fun y ↦ (1 + β * ξ t y)⁻¹ := funext (hS t ht).1
    rw [heq]
    simpa only [D, BUC.smul_apply, BUC.smulBUC_apply, (hS t ht).1, smul_smul,
      smul_eq_mul, pow_two] using! hasFDerivAt_coleHopfInv_slope (hd t ht x).1 hx
  have hDnorm : ‖D t‖ ≤ (4 * |β|) * ‖q t‖ := by
    have hS2 : ‖BUC.smulBUC (S t) (S t)‖ ≤ 4 :=
      (BUC.norm_smulBUC_le _ _).trans (by nlinarith [(hS t ht).2, norm_nonneg (S t)])
    calc
      _ = |β| * ‖BUC.smulBUC (BUC.smulBUC (S t) (S t)) (q t)‖ := by
        simp only [D, norm_smul, norm_neg, Real.norm_eq_abs]
      _ ≤ |β| * (4 * ‖q t‖) := by
        gcongr
        exact (BUC.norm_smulBUC_le _ _).trans (mul_le_mul_of_nonneg_right hS2 (norm_nonneg _))
      _ = _ := by ring
  refine ⟨?_, (BUC.norm_smulBUC_le _ _).trans
    (mul_le_mul_of_nonneg_right (hS t ht).2 (norm_nonneg _)), ?_⟩
  · intro x
    constructor
    · have hx : ξ t x ∈ coleHopfDomain β :=
        Icc_subset_coleHopfDomain_of_small_radius (hsmall t ht) (abs_le.mp ((ξ t).norm_apply_le x))
      have heq : (σ t : E → ℝ) = coleHopfInv β ∘ ξ t := funext (hσ t ht)
      rw [heq]
      simpa only [Q, BUC.smulBUC_apply, (hS t ht).1] using!
        (hasDerivAt_coleHopfInv hx).comp_hasFDerivAt x (hd t ht x).1
    · simpa only [Q, H, BUC.add_apply, BUC.smulBUC_apply, BUC.bilinearBUC_apply,
        ContinuousLinearMap.smulRightL_apply_apply] using! (hSd x).smul (hd t ht x).2
  · calc
      ‖H t‖ ≤ ‖BUC.smulBUC (S t) (h t)‖ +
          ‖BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (D t) (q t)‖ :=
        norm_add_le _ _
      _ ≤ 2 * ‖h t‖ + ((4 * |β|) * ‖q t‖) * ‖q t‖ := add_le_add
        ((BUC.norm_smulBUC_le _ _).trans (mul_le_mul_of_nonneg_right (hS t ht).2 (norm_nonneg _)))
        ((norm_bilinear_smulRightBUC_le _ _).trans (mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)))
      _ = _ := by ring

variable [FiniteDimensional ℝ E]

/-- Taking the trace of the actual Hessian supplies the BUC Laplacian
with its uniform bound, not merely a pointwise formal expression. -/
theorem exists_coleHopfInv_buc_laplacian {β T : ℝ} {ξ σ : ℝ → BUC E ℝ}
    (hξ : ContinuousOn ξ (Icc 0 T)) (q : ℝ → BUC E (E →L[ℝ] ℝ))
    (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ))
    (hqc : ContinuousOn q (Icc 0 T)) (hhc : ContinuousOn h (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x)
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hσ : ∀ t ∈ Icc 0 T, ∀ x, σ t x = coleHopfInv β (ξ t x)) :
    ∃ L : ℝ → BUC E ℝ, ContinuousOn L (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, (∀ x, L t x = Δ (σ t : E → ℝ) x) ∧
        ‖L t‖ ≤ ‖laplacianTraceCLM (E := E) (F := ℝ)‖ *
          (2 * ‖h t‖ + (4 * |β|) * ‖q t‖ ^ 2) := by
  obtain ⟨Q, H, _, hHc, hb⟩ := exists_coleHopfInv_buc_second_fderivative hξ q h hqc hhc hd hsmall hσ
  let A : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ := laplacianTraceCLM
  refine ⟨fun t ↦ BUC.postcompCLM A (H t), (BUC.postcompCLM A).continuous.comp_continuousOn hHc, ?_⟩
  intro t ht
  refine ⟨fun x ↦ (laplacian_eq_trace_of_hasFDerivAt (σ t) (Q t) (H t)
    (fun y ↦ ((hb t ht).1 y).1) (fun y ↦ ((hb t ht).1 y).2) x).symm, ?_⟩
  exact (BUC.norm_postcompCLM_apply_le A (H t)).trans
    (mul_le_mul_of_nonneg_left (hb t ht).2.2 (norm_nonneg _))

end

end Planarwave
