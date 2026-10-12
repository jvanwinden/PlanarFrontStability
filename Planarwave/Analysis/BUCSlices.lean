/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC

@[expose] public section

/-!
# BUC functions as uniformly continuous families of slices

A jointly BUC function on a product gives a BUC family of longitudinal BUC
slices. This is a norm-preserving embedding; no converse assertion about joint
uniform continuity of arbitrary BUC-valued families is needed.
-/

namespace BUC

noncomputable section

variable {V W E 𝕜 : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedAddCommGroup E]

/-- Fix the first variable of a jointly bounded uniformly continuous function. -/
def slice (v : BUC (V × W) E) (y : V) : BUC W E :=
  v.comp (fun z ↦ (y, z)) (uniformContinuous_const.prodMk uniformContinuous_id)

@[simp]
theorem slice_apply (v : BUC (V × W) E) (y : V) (z : W) : slice v y z = v (y, z) := rfl

theorem norm_slice_le (v : BUC (V × W) E) (y : V) : ‖slice v y‖ ≤ ‖v‖ :=
  norm_comp_le _ _ _

/-- Uniform continuity in the transverse coordinate holds in the slice supremum norm. -/
theorem uniformContinuous_slice (v : BUC (V × W) E) : UniformContinuous (slice v) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hv⟩ := Metric.uniformContinuous_iff.mp v.uniformContinuous (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun y y' hyy' ↦ ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((norm_le (by positivity : 0 ≤ ε / 2)).mpr ?_) (half_lt_self hε)
  intro z
  change ‖v (y, z) - v (y', z)‖ ≤ ε / 2
  rw [← dist_eq_norm]
  apply (hv ?_).le
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist y y')] using hyy'

/-- Regard a jointly BUC function as a BUC family of slices. -/
def curry (v : BUC (V × W) E) : BUC V (BUC W E) where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup (slice v)
    (uniformContinuous_slice v).continuous ‖v‖ (norm_slice_le v)
  uniformContinuous' := uniformContinuous_slice v

@[simp]
theorem curry_apply (v : BUC (V × W) E) (y : V) (z : W) : curry v y z = v (y, z) := rfl

theorem norm_curry_le (v : BUC (V × W) E) : ‖curry v‖ ≤ ‖v‖ :=
  (norm_le (norm_nonneg v)).mpr (norm_slice_le v)

/-- The embedding preserves the full supremum norm. -/
theorem norm_curry (v : BUC (V × W) E) : ‖curry v‖ = ‖v‖ := by
  apply le_antisymm (norm_curry_le v)
  apply (norm_le (norm_nonneg _)).mpr
  rintro ⟨y, z⟩
  exact (norm_apply_le (curry v y) z).trans (norm_apply_le (curry v) y)

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

/-- The slicing embedding as a continuous linear map. -/
def curryCLM : BUC (V × W) E →L[𝕜] BUC V (BUC W E) :=
  LinearMap.mkContinuous
    { toFun := fun v : BUC (V × W) E ↦ curry v
      map_add' := by intros; ext y z; rfl
      map_smul' := by intros; ext y z; rfl }
    1 fun v ↦ by
      change ‖curry v‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact norm_curry_le v

@[simp]
theorem curryCLM_apply (v : BUC (V × W) E) : curryCLM (𝕜 := 𝕜) v = curry v := rfl

end

end BUC
