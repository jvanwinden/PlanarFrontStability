/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ColeHopfInverseHigherBounds

@[expose] public section

/-!
# Time-continuous higher spatial derivatives of the inverse phase

Repeatedly differentiate the reciprocal slope, then the inverse transform.
This constructs the actual BUC derivative trajectories at every finite
order; pointwise spatial smoothness alone would not imply this property.
-/

open Set

namespace Planarwave

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Higher spatial BUC regularity of an inverse-slope trajectory. -/
theorem BUCSpatialRegularOn.coleHopfInvSlope {k : ℕ} {β T : ℝ}
    {ξ S : ℝ → BUC E ℝ} (hξ : BUCSpatialRegularOn (Icc 0 T) k ξ)
    (hSc : ContinuousOn S (Icc 0 T))
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hS : ∀ t ∈ Icc 0 T, ∀ x, S t x = (1 + β * ξ t x)⁻¹) :
    BUCSpatialRegularOn (Icc 0 T) k S := by
  induction k with
  | zero => exact hSc
  | succ k ih =>
    have hSk := ih hξ.of_succ
    obtain ⟨_, q, hq, hd⟩ := hξ
    let Q := fun t ↦ (-β) • BUC.smulBUC (BUC.smulBUC (S t) (S t)) (q t)
    refine ⟨hSc, Q, ?_, ?_⟩
    · exact ((hSk.bilinear hSk (ContinuousLinearMap.lsmul ℝ ℝ)).bilinear hq
        (ContinuousLinearMap.lsmul ℝ ℝ)).const_smul (-β)
    · intro t ht x
      have hx : |β * ξ t x| ≤ 1 / 2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left ((ξ t).norm_apply_le x) (abs_nonneg β)).trans
          (hsmall t ht)
      have heq : (S t : E → ℝ) = fun y ↦ (1 + β * ξ t y)⁻¹ := funext (hS t ht)
      rw [heq]
      simpa only [Q, BUC.smul_apply, BUC.smulBUC_apply, hS t ht,
        smul_smul, smul_eq_mul, pow_two] using!
        hasFDerivAt_coleHopfInv_slope (hd t ht x) hx

/-- Higher spatial derivatives of the inverse phase are continuous in BUC norm. -/
theorem BUCSpatialRegularOn.coleHopfInv {k : ℕ} {β T : ℝ}
    {ξ σ : ℝ → BUC E ℝ} (hξ : BUCSpatialRegularOn (Icc 0 T) k ξ)
    (hσc : ContinuousOn σ (Icc 0 T))
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hσ : ∀ t ∈ Icc 0 T, ∀ x, σ t x = coleHopfInv β (ξ t x)) :
    BUCSpatialRegularOn (Icc 0 T) k σ := by
  cases k with
  | zero => exact hσc
  | succ k =>
    obtain ⟨S, hSc, hS⟩ := exists_continuous_coleHopfInvSlope_on ξ hξ.continuous hsmall
    have hSk := hξ.of_succ.coleHopfInvSlope hSc hsmall (fun t ht ↦ (hS t ht).1)
    obtain ⟨_, q, hq, hd⟩ := hξ
    refine ⟨hσc, fun t ↦ BUC.smulBUC (S t) (q t),
      hSk.bilinear hq (ContinuousLinearMap.lsmul ℝ ℝ), ?_⟩
    intro t ht x
    have hx : ξ t x ∈ coleHopfDomain β :=
      Icc_subset_coleHopfDomain_of_small_radius (hsmall t ht)
        (abs_le.mp ((ξ t).norm_apply_le x))
    have heq : (σ t : E → ℝ) = Planarwave.coleHopfInv β ∘ ξ t := funext (hσ t ht)
    rw [heq, BUC.smulBUC_apply, (hS t ht).1 x]
    exact (hasDerivAt_coleHopfInv hx).comp_hasFDerivAt x (hd t ht x)

end

end Planarwave
