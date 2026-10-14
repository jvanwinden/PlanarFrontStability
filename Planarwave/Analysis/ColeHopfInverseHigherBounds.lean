/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ColeHopfInverseSecondDerivative
public import Planarwave.Analysis.BUCSpatialBounds

@[expose] public section

/-!
# Uniform higher derivative bounds for the inverse Cole--Hopf map

This is the quantitative smooth-inverse step in Step 1 of `lem:key`.
First bound the derivatives of the reciprocal slope by differentiating
`S = (1 + β ξ)⁻¹`, so that `DS = -β S² Dξ`. Then `Dσ = S Dξ`
retains the small factor in the `C^k` bound on ξ. Constants depend only
on the order, β, and a fixed upper bound on the `C^k` norm, not on time.
-/

namespace Planarwave

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A common derivative bound for the reciprocal slope on the small range. -/
def coleHopfInvSlopeSpatialConstant (β B : ℝ) : ℕ → ℝ
  | 0 => 2
  | k + 1 => max 2 (|β| * ((2 : ℝ) ^ k *
      ((2 : ℝ) ^ k * coleHopfInvSlopeSpatialConstant β B k *
        coleHopfInvSlopeSpatialConstant β B k) * B))

theorem two_le_coleHopfInvSlopeSpatialConstant (β B : ℝ) (k : ℕ) :
    2 ≤ coleHopfInvSlopeSpatialConstant β B k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

/-- The reciprocal slope has bounded genuine BUC derivatives at every finite order. -/
theorem BUCSpatialBound.coleHopfInvSlope {k : ℕ} {β A B : ℝ} {ξ : BUC E ℝ}
    (hξ : BUCSpatialBound k ξ A) (hAB : A ≤ B) (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) :
    BUCSpatialBound k (coleHopfInvSlopeSmallBUC β ξ hsmall)
      (coleHopfInvSlopeSpatialConstant β B k) := by
  induction k with
  | zero => exact norm_coleHopfInvSlopeSmallBUC_le β ξ hsmall
  | succ k ih =>
    have hS := ih hξ.of_succ
    obtain ⟨_, q, hq, hd⟩ := hξ
    let S := coleHopfInvSlopeSmallBUC β ξ hsmall
    let Q := (-β) • BUC.smulBUC (BUC.smulBUC S S) q
    refine ⟨(norm_coleHopfInvSlopeSmallBUC_le β ξ hsmall).trans
      (two_le_coleHopfInvSlopeSpatialConstant β B (k + 1)), Q, ?_, ?_⟩
    · apply (((hS.smulBUC hS).smulBUC (hq.mono hAB)).smul (-β)).mono
      simpa only [abs_neg, coleHopfInvSlopeSpatialConstant] using
        (le_max_right 2 (|β| * ((2 : ℝ) ^ k *
          ((2 : ℝ) ^ k * coleHopfInvSlopeSpatialConstant β B k *
            coleHopfInvSlopeSpatialConstant β B k) * B)))
    · intro x
      have hx : |β * ξ x| ≤ 1 / 2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (ξ.norm_apply_le x) (abs_nonneg β)).trans hsmall
      simpa only [Q, S, coleHopfInvSlopeSmallBUC_apply, BUC.smul_apply,
        BUC.smulBUC_apply, smul_smul, smul_eq_mul, pow_two] using!
        hasFDerivAt_coleHopfInv_slope (hd x) hx

/-- The constant multiplying the small transformed-field bound. -/
def coleHopfInvSpatialConstant (β B : ℝ) : ℕ → ℝ
  | 0 => 2
  | k + 1 => max 2 ((2 : ℝ) ^ k * coleHopfInvSlopeSpatialConstant β B k)

theorem two_le_coleHopfInvSpatialConstant (β B : ℝ) (k : ℕ) :
    2 ≤ coleHopfInvSpatialConstant β B k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

/-- The inverse transform preserves the small factor in a uniform `C^k` estimate. -/
theorem BUCSpatialBound.coleHopfInv {k : ℕ} {β A B : ℝ} {ξ : BUC E ℝ}
    (hξ : BUCSpatialBound k ξ A) (hAB : A ≤ B) (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) :
    BUCSpatialBound k (coleHopfInvSmallBUC β ξ hsmall)
      (coleHopfInvSpatialConstant β B k * A) := by
  have hA := hξ.nonneg
  have hn : ‖coleHopfInvSmallBUC β ξ hsmall‖ ≤ 2 * A :=
    (norm_coleHopfInvSmallBUC_le β ξ hsmall).trans (by gcongr; exact hξ.norm_le)
  cases k with
  | zero => exact hn
  | succ k =>
    have hS := hξ.of_succ.coleHopfInvSlope hAB hsmall
    obtain ⟨_, q, hq, hd⟩ := hξ
    refine ⟨hn.trans (mul_le_mul_of_nonneg_right
      (two_le_coleHopfInvSpatialConstant β B (k + 1)) hA),
      BUC.smulBUC (coleHopfInvSlopeSmallBUC β ξ hsmall) q,
      (hS.smulBUC hq).mono (mul_le_mul_of_nonneg_right (le_max_right _ _) hA), ?_⟩
    intro x
    have hx : ξ x ∈ coleHopfDomain β :=
      Icc_subset_coleHopfDomain_of_small_radius hsmall (abs_le.mp (ξ.norm_apply_le x))
    simpa only [coleHopfInvSmallBUC_apply, BUC.smulBUC_apply,
      coleHopfInvSlopeSmallBUC_apply] using!
      (hasDerivAt_coleHopfInv hx).comp_hasFDerivAt x (hd x)

end

end Planarwave
