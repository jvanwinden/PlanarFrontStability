/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialBounds

@[expose] public section

/-!
# Quantitative spatial chain rules on BUC

Repeated chain and product rules transfer common bounds on genuine BUC
derivatives through a uniformly continuous change of coordinates. The
coordinate map itself need not be bounded; only its derivatives are.
This is important for the modulation shear in Step 4 of `lem:key`.
-/

namespace Planarwave

noncomputable section

universe u v

variable {X E : Type} {F : Type u} {G : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace BUCSpatialBound

/-- The derivative witnesses in a common bound imply the usual spatial smoothness. -/
theorem contDiff {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A) :
    ContDiff ℝ k (f : E → F) := by
  induction k generalizing F with
  | zero => exact contDiff_zero.mpr f.continuous
  | succ k ih =>
    obtain ⟨_, q, hq, hd⟩ := hf
    exact contDiff_succ_iff_hasFDerivAt.mpr ⟨q, ih hq, hd⟩

theorem const (k : ℕ) (a : F) : BUCSpatialBound k (BUC.const E a) ‖a‖ := by
  induction k generalizing F with
  | zero => exact BUC.norm_const_le a
  | succ k ih =>
    refine ⟨BUC.norm_const_le a, BUC.const E (0 : E →L[ℝ] F),
      (ih (0 : E →L[ℝ] F)).mono (by simp), ?_⟩
    intro x
    exact hasFDerivAt_const a x

/-- Linear postcomposition costs just the operator norm at every derivative order. -/
theorem postcomp {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A)
    (L : F →L[ℝ] G) : BUCSpatialBound k (BUC.postcompCLM L f) (‖L‖ * A) := by
  have hA := hf.nonneg
  induction k generalizing F G with
  | zero =>
    exact (BUC.norm_postcompCLM_apply_le L f).trans
      (mul_le_mul_of_nonneg_left hf (norm_nonneg L))
  | succ k ih =>
    obtain ⟨hn, q, hq, hd⟩ := hf
    let _ : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
    let _ : NormedAddCommGroup (E →L[ℝ] G) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] G) := inferInstance
    let J := ContinuousLinearMap.compL ℝ E F G L
    have hJ : ‖J‖ ≤ ‖L‖ := by
      apply J.opNorm_le_bound (norm_nonneg L)
      intro q
      exact ContinuousLinearMap.opNorm_comp_le L q
    refine ⟨(BUC.norm_postcompCLM_apply_le L f).trans (by gcongr),
      BUC.postcompCLM J q, (ih hq J).mono (mul_le_mul_of_nonneg_right hJ hA), ?_⟩
    intro x
    simpa only [BUC.postcompCLM_apply, J, ContinuousLinearMap.compL_apply] using!
      L.hasFDerivAt.comp x (hd x)

/-- Pullback by a contractive linear coordinate projection preserves the common bound. -/
theorem precomp_contraction {k : ℕ} {f : BUC E F} {A : ℝ}
    (hf : BUCSpatialBound k f A) (L : X →L[ℝ] E) (hL : ‖L‖ ≤ 1) :
    BUCSpatialBound k (f.comp L L.uniformContinuous) A := by
  have hA := hf.nonneg
  induction k generalizing F with
  | zero => exact (BUC.norm_comp_le f L L.uniformContinuous).trans hf
  | succ k ih =>
    obtain ⟨hn, q, hq, hd⟩ := hf
    let _ : NormedAddCommGroup (X →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (X →L[ℝ] F) := inferInstance
    let _ : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
    let J := (ContinuousLinearMap.compL ℝ X E F).flip L
    have hJ : ‖J‖ ≤ 1 := by
      calc
        _ ≤ ‖(ContinuousLinearMap.compL ℝ X E F).flip‖ * ‖L‖ :=
          ((ContinuousLinearMap.compL ℝ X E F).flip).le_opNorm L
        _ ≤ 1 * 1 := by
          gcongr
          rw [ContinuousLinearMap.opNorm_flip]
          exact ContinuousLinearMap.norm_compL_le ℝ X E F
        _ = _ := one_mul _
    refine ⟨(BUC.norm_comp_le f L L.uniformContinuous).trans hn,
      BUC.postcompCLM J (q.comp L L.uniformContinuous),
      ((ih hq).postcomp J).mono (by nlinarith), ?_⟩
    intro x
    exact (hd (L x)).comp x L.hasFDerivAt

end BUCSpatialBound

/-- A finite-order chain-rule constant when all derivatives of the coordinate
map of positive order are bounded by `B`. -/
def bucSpatialCompositionConstant (B : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => max 1 ((2 : ℝ) ^ k * bucSpatialCompositionConstant B k * B)

theorem one_le_bucSpatialCompositionConstant (B : ℝ) (k : ℕ) :
    1 ≤ bucSpatialCompositionConstant B k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

/-- Quantitative chain rule. The inner coordinate map may be unbounded;
its derivative is a genuine BUC field with bounds through order `k - 1`. -/
theorem BUCSpatialBound.comp {k : ℕ} {f : BUC E F} {A B : ℝ}
    (hf : BUCSpatialBound k f A) (g : X → E) (hg : UniformContinuous g)
    (q : BUC X (X →L[ℝ] E)) (hd : ∀ x, HasFDerivAt g (q x) x)
    (hq : BUCSpatialBound (k - 1) q B) :
    BUCSpatialBound k (f.comp g hg) (bucSpatialCompositionConstant B k * A) := by
  have hA := hf.nonneg
  have hB := hq.nonneg
  induction k generalizing F with
  | zero => simpa only [BUCSpatialBound, bucSpatialCompositionConstant, one_mul] using
      (BUC.norm_comp_le f g hg).trans hf
  | succ k ih =>
    obtain ⟨hn, f', hf', hdf⟩ := hf
    have hqk : BUCSpatialBound k q B := hq
    have hqp : BUCSpatialBound (k - 1) q B := by
      cases k with
      | zero => exact hqk
      | succ k => exact hqk.of_succ
    have hcomp := ih hf' hqp
    let _ : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
    let _ : NormedAddCommGroup (X →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (X →L[ℝ] F) := inferInstance
    let _ : NormedAddCommGroup (X →L[ℝ] E) := inferInstance
    let _ : NormedSpace ℝ (X →L[ℝ] E) := inferInstance
    let _ : NormedAddCommGroup ((X →L[ℝ] E) →L[ℝ] X →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ ((X →L[ℝ] E) →L[ℝ] X →L[ℝ] F) := inferInstance
    let J := ContinuousLinearMap.compL ℝ X E F
    have hder := hcomp.bilinear hqk J
    have hderbound : (2 : ℝ) ^ k * ‖J‖ * (bucSpatialCompositionConstant B k * A) * B ≤
        bucSpatialCompositionConstant B (k + 1) * A := by
      calc
        _ ≤ (2 : ℝ) ^ k * 1 * (bucSpatialCompositionConstant B k * A) * B := by
          gcongr
          · exact mul_nonneg (by linarith [one_le_bucSpatialCompositionConstant B k]) hA
          · exact ContinuousLinearMap.norm_compL_le ℝ X E F
        _ = ((2 : ℝ) ^ k * bucSpatialCompositionConstant B k * B) * A := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hA
    refine ⟨(BUC.norm_comp_le f g hg).trans (hn.trans ?_),
      BUC.bilinearBUC J (f'.comp g hg) q, hder.mono hderbound, ?_⟩
    · exact le_mul_of_one_le_left hA (one_le_bucSpatialCompositionConstant B (k + 1))
    · intro x
      exact (hdf (g x)).comp x (hd x)

end

end Planarwave
