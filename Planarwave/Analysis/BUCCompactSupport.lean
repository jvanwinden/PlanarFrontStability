/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

namespace BUC

noncomputable section

variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F]

/-- Compactly supported continuous tests belong to the BUC space. -/
def ofCompactSupport (f : X → F) (hf : Continuous f) (hc : HasCompactSupport f) : BUC X F :=
  { toBCF :=
      { toFun := f
        continuous_toFun := hf
        map_bounded' := by
          obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
          exact ⟨2 * C, fun x y ↦ (dist_le_norm_add_norm _ _).trans
            (by linarith [hC ⟨x, rfl⟩, hC ⟨y, rfl⟩])⟩ }
    uniformContinuous' := hc.uniformContinuous_of_continuous hf }

@[simp]
theorem ofCompactSupport_apply (f : X → F) (hf : Continuous f) (hc : HasCompactSupport f)
    (x : X) : ofCompactSupport f hf hc x = f x := rfl

variable [MeasurableSpace X] [BorelSpace X] [NormedSpace ℝ F]

/-- A bounded scalar test can multiply an integrable vector-valued weight. -/
theorem integrable_smul (a : BUC X ℝ) {f : X → F} {μ : MeasureTheory.Measure X}
    (hf : MeasureTheory.Integrable f μ) : MeasureTheory.Integrable (fun x ↦ a x • f x) μ := by
  refine (hf.norm.const_mul ‖a‖).mono'
    (a.continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
  exact MeasureTheory.ae_of_all _ fun x ↦ by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (a.norm_apply_le x) (norm_nonneg _)

end

end BUC
