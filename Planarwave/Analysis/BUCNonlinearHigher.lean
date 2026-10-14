/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialComposition

@[expose] public section

/-!
# Smooth reaction maps on spatial BUC spaces

Only bounded state ranges are used: the reaction and its derivatives need
not be globally bounded or Lipschitz. Compactness gives constants before
the spatial function is chosen, and repeated chain rules preserve genuine
BUC derivative fields and their norm continuity in time. These are the
nonlinear-composition inputs to the parabolic bootstrap in Step 4.
-/

open Set
open scoped ContDiff

namespace BUC

noncomputable section

variable {A V F : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ V] [NormedSpace ℝ F] in
/-- A continuous reaction is uniformly bounded on every bounded BUC ball. -/
theorem exists_postcompContinuous_norm_bound (f : V → F) (hf : Continuous f) (R : ℝ) :
    ∃ C > 0, ∀ u : BUC A V, ‖u‖ ≤ R → ‖postcompContinuous f hf u‖ ≤ C := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun u hu ↦ ?_⟩
  apply (BUC.norm_le (le_trans zero_le_one (le_max_right _ _))).mpr
  intro x
  exact (hK (u x) (by simpa only [Metric.mem_closedBall, dist_zero_right] using
    (u.norm_apply_le x).trans hu)).trans (le_max_left _ _)

/-- The local Lipschitz constant depends on the reaction and state radius,
not on the two BUC fields. This also applies to derivatives of the reaction. -/
theorem exists_postcompContinuous_lipschitz_bound (f : V → F) (hf : ContDiff ℝ 1 f)
    (R : ℝ) :
    ∃ L > 0, ∀ u v : BUC A V, ‖u‖ ≤ R → ‖v‖ ≤ R →
      ‖postcompContinuous f hf.continuous u - postcompContinuous f hf.continuous v‖ ≤
        L * ‖u - v‖ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  let L := max K 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨L, hL, fun u v hu hv ↦ ?_⟩
  apply (BUC.norm_le (mul_nonneg hL.le (norm_nonneg _))).mpr
  intro x
  have hx (w : BUC A V) (hw : ‖w‖ ≤ R) : w x ∈ Metric.closedBall (0 : V) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (w.norm_apply_le x).trans hw
  have hpoint := (convex_closedBall (0 : V) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hf.differentiable (by norm_num) z)
    (fun z hz ↦ (hK z hz).trans (le_max_left K 1)) (hx v hv) (hx u hu)
  exact hpoint.trans (mul_le_mul_of_nonneg_left ((u - v).norm_apply_le x) hL.le)

/-- Smooth substitution is continuous in the BUC norm, without a global
bound on the derivative of the reaction. -/
theorem continuous_postcompContinuous (f : V → F) (hf : ContDiff ℝ 1 f) :
    Continuous (postcompContinuous (A := A) f hf.continuous) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  obtain ⟨L, hL, hb⟩ := exists_postcompContinuous_lipschitz_bound (A := A) f hf (‖u‖ + 1)
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min 1 (ε / (L + 1)), lt_min zero_lt_one (div_pos hε (by linarith)), ?_⟩
  intro v hv
  have hv1 : ‖v - u‖ < 1 := by simpa only [dist_eq_norm] using hv.trans_le (min_le_left _ _)
  have hvu : ‖v‖ ≤ ‖u‖ + 1 := by
    have hn := norm_le_norm_add_norm_sub u v
    rw [norm_sub_rev u v] at hn
    linarith
  rw [dist_eq_norm]
  apply (hb v u hvu (by linarith)).trans_lt
  have hvε : ‖v - u‖ < ε / (L + 1) := by
    simpa only [dist_eq_norm] using hv.trans_le (min_le_right _ _)
  have hh := (lt_div_iff₀ (show 0 < L + 1 by linarith)).mp hvε
  nlinarith [norm_nonneg (v - u)]

end

end BUC

namespace Planarwave

noncomputable section

universe u

variable {E V : Type} {F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth reaction preserves finite-order BUC bounds uniformly on a
fixed `C^k` ball. The constant precedes the choice of the spatial field. -/
theorem exists_bucSpatialBound_postcomp (k : ℕ) (f : V → F) (hf : ContDiff ℝ ∞ f)
    (B : ℝ) :
    ∃ C > 0, ∀ u : BUC E V, BUCSpatialBound k u B →
      BUCSpatialBound k (BUC.postcompContinuous f hf.continuous u) C := by
  induction k generalizing F with
  | zero => exact BUC.exists_postcompContinuous_norm_bound f hf.continuous B
  | succ k ih =>
    have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    obtain ⟨A, hA, hAb⟩ := ih (fderiv ℝ f) hf'
    obtain ⟨C₀, hC₀, hC₀b⟩ := BUC.exists_postcompContinuous_norm_bound (A := E) f hf.continuous B
    let _ : NormedAddCommGroup (V →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (V →L[ℝ] F) := inferInstance
    let _ : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] V) := inferInstance
    let _ : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
    let _ : NormedAddCommGroup ((E →L[ℝ] V) →L[ℝ] E →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ ((E →L[ℝ] V) →L[ℝ] E →L[ℝ] F) := inferInstance
    let J := ContinuousLinearMap.compL ℝ E V F
    let C := max C₀ ((2 : ℝ) ^ k * ‖J‖ * A * B)
    refine ⟨C, hC₀.trans_le (le_max_left _ _), fun u hu ↦ ?_⟩
    have huk := hu.of_succ
    obtain ⟨hun, q, hq, hd⟩ := hu
    refine ⟨(hC₀b u hun).trans (le_max_left _ _),
      BUC.bilinearBUC J (BUC.postcompContinuous (fderiv ℝ f) hf'.continuous u) q,
      ((hAb u huk).bilinear hq J).mono (le_max_right _ _), ?_⟩
    intro x
    exact (hf.differentiable (by simp) (u x)).hasFDerivAt.comp x (hd x)

/-- All source derivatives remain norm-continuous in time under smooth
reaction composition. No compactness of the spatial domain is used. -/
theorem BUCSpatialRegularOn.postcomp_smooth {s : Set ℝ} {k : ℕ} {u : ℝ → BUC E V}
    (hu : BUCSpatialRegularOn s k u) (f : V → F) (hf : ContDiff ℝ ∞ f) :
    BUCSpatialRegularOn s k (fun t ↦ BUC.postcompContinuous f hf.continuous (u t)) := by
  induction k generalizing F with
  | zero => exact (BUC.continuous_postcompContinuous f (hf.of_le (by simp))).comp_continuousOn hu
  | succ k ih =>
    have huk := hu.of_succ
    obtain ⟨hc, q, hq, hd⟩ := hu
    have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    let J := ContinuousLinearMap.compL ℝ E V F
    refine ⟨(BUC.continuous_postcompContinuous f (hf.of_le (by simp))).comp_continuousOn hc,
      fun t ↦ BUC.bilinearBUC J (BUC.postcompContinuous (fderiv ℝ f) hf'.continuous (u t)) (q t),
      (ih huk (fderiv ℝ f) hf').bilinear hq J, ?_⟩
    intro t ht x
    exact (hf.differentiable (by simp) (u t x)).hasFDerivAt.comp x (hd t ht x)

end

end Planarwave
