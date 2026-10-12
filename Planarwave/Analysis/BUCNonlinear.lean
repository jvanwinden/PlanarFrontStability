/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCBilinear
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Nonlinear composition and Taylor remainders on BUC

Continuous nonlinear maps preserve BUC when the values lie in a proper space.
On bounded sets, a twice continuously differentiable reaction has a uniform
quadratic Taylor remainder. This is the reaction estimate in Lemma 4.1 of the paper.
-/

open Bornology Function Set

noncomputable section

namespace BUC

section PointwiseBounds

variable {A F G : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Multiplication by a real BUC scalar field. -/
def smulBUC (a : BUC A ℝ) (v : BUC A F) : BUC A F :=
  bilinearBUC (ContinuousLinearMap.lsmul ℝ ℝ) a v

@[simp]
theorem smulBUC_apply (a : BUC A ℝ) (v : BUC A F) (x : A) :
    smulBUC a v x = a x • v x := rfl

theorem norm_smulBUC_le (a : BUC A ℝ) (v : BUC A F) :
    ‖smulBUC a v‖ ≤ ‖a‖ * ‖v‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  rw [smulBUC_apply, norm_smul]
  exact mul_le_mul (a.norm_apply_le x) (v.norm_apply_le x) (norm_nonneg _) (norm_nonneg _)

/-- Pointwise operator application has the expected product supremum-norm bound. -/
theorem norm_operatorApply_le (a : BUC A (F →L[ℝ] G)) (v : BUC A F) :
    ‖operatorApply a v‖ ≤ ‖a‖ * ‖v‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  exact ((a x).le_opNorm (v x)).trans
    (mul_le_mul (a.norm_apply_le x) (v.norm_apply_le x) (norm_nonneg (v x)) (norm_nonneg a))

end PointwiseBounds

variable {A E F : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]

/-- Continuous postcomposition is uniformly continuous on the compact closure
of the range of a BUC function. No global uniform continuity of the nonlinearity is needed. -/
theorem uniformContinuous_postcomp {f : E → F} (hf : Continuous f) (v : BUC A E) :
    UniformContinuous (f ∘ v) := by
  have hK : IsCompact (closure (range v)) := v.isBounded_range.isCompact_closure
  exact uniformContinuousOn_univ.mp
    ((hK.uniformContinuousOn_of_continuous hf.continuousOn).comp
      v.uniformContinuous.uniformContinuousOn (fun x _ ↦ subset_closure (mem_range_self x)))

/-- Continuous nonlinear postcomposition on BUC, using compactness of the value range. -/
def postcompContinuous (f : E → F) (hf : Continuous f) (v : BUC A E) : BUC A F where
  toBCF :=
    { toFun := f ∘ v
      continuous_toFun := hf.comp v.continuous
      map_bounded' := Metric.isBounded_range_iff.mp <| by
        apply ((v.isBounded_range.isCompact_closure).image hf).isBounded.subset
        rintro _ ⟨x, rfl⟩
        exact ⟨v x, subset_closure (mem_range_self x), rfl⟩ }
  uniformContinuous' := uniformContinuous_postcomp hf v

@[simp]
theorem postcompContinuous_apply (f : E → F) (hf : Continuous f) (v : BUC A E) (x : A) :
    postcompContinuous f hf v x = f (v x) := rfl

end BUC

namespace Planarwave

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniform second-order Taylor estimate on every bounded ball.
Bound the second derivative on the compact ball, then apply the mean value
estimate to the first derivative and to the first-order Taylor remainder. -/
theorem exists_quadratic_taylor_bound_closedBall {f : E → F} (hf : ContDiff ℝ 2 f) (R : ℝ) :
    ∃ C > 0, ∀ x ∈ Metric.closedBall (0 : E) R, ∀ y ∈ Metric.closedBall (0 : E) R,
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    (hf'.continuous_fderiv (by norm_num)).continuousOn
  let C := max K 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ z ∈ Metric.closedBall (0 : E) R,
      ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C := fun z hz ↦ (hK z hz).trans (le_max_left _ _)
  have hfirst (x y : E) (hx : x ∈ Metric.closedBall (0 : E) R)
      (hy : y ∈ Metric.closedBall (0 : E) R) :
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y - x‖ :=
    (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hf'.differentiable (by norm_num) z) hbound hx hy
  refine ⟨C, hC, fun x hx y hy ↦ ?_⟩
  have hsegment := (convex_closedBall (0 : E) R).segment_subset hx hy
  have hb : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
    intro z hz
    exact (hfirst x z hx (hsegment hz)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hC.le)
  simpa only [pow_two, mul_assoc] using
    (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ ↦ hf.differentiable (by norm_num) z) hb
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

end Planarwave

namespace BUC

variable {A E F : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact nonlinear reaction remainder about a bounded background. -/
def reactionRemainder (f : E → F) (hf : ContDiff ℝ 2 f) (p v : BUC A E) : BUC A F :=
  postcompContinuous f hf.continuous (p + v) - postcompContinuous f hf.continuous p -
    operatorApply (postcompContinuous (fderiv ℝ f) (hf.continuous_fderiv (by norm_num)) p) v

@[simp]
theorem reactionRemainder_apply (f : E → F) (hf : ContDiff ℝ 2 f)
    (p v : BUC A E) (x : A) :
    reactionRemainder f hf p v x = f (p x + v x) - f (p x) - fderiv ℝ f (p x) (v x) := rfl

/-- The quadratic reaction bound is uniform over all perturbations in a fixed BUC ball. -/
theorem exists_reactionRemainder_bound (f : E → F) (hf : ContDiff ℝ 2 f)
    (p : BUC A E) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ v : BUC A E, ‖v‖ ≤ R → ‖reactionRemainder f hf p v‖ ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := Planarwave.exists_quadratic_taylor_bound_closedBall hf (‖p‖ + R)
  refine ⟨C, hC, fun v hv ↦ ?_⟩
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  have hp : p x ∈ Metric.closedBall (0 : E) (‖p‖ + R) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (p.norm_apply_le x).trans (le_add_of_nonneg_right hR)
  have hpv : p x + v x ∈ Metric.closedBall (0 : E) (‖p‖ + R) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (p.norm_apply_le x) ((v.norm_apply_le x).trans hv))
  have hpoint : ‖reactionRemainder f hf p v x‖ ≤ C * ‖v x‖ ^ 2 := by
    simpa only [reactionRemainder_apply, add_sub_cancel_left] using hb (p x) hp (p x + v x) hpv
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (v.norm_apply_le x) 2) hC.le)

end BUC
