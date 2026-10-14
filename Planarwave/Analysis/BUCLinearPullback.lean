/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialComposition

@[expose] public section

/-!
# Linear changes of spatial coordinates in BUC derivative bounds

A continuous linear change of coordinates preserves the genuine BUC spatial
derivative hierarchy. No contractivity or compatibility of the two norms is
assumed; the quantitative bound records the operator norm of the coordinate
map. In particular, this applies to the Euclidean-to-product coordinates used
in the modulation estimates.
-/

namespace Planarwave

noncomputable section

universe u v

variable {X E : Type} {F : Type u} {G : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A linear coordinate change incurs only the finite-order chain-rule constant. -/
theorem BUCSpatialBound.precompCLM {k : ℕ} {f : BUC E F} {A : ℝ}
    (hf : BUCSpatialBound k f A) (L : X →L[ℝ] E) :
    BUCSpatialBound k (f.comp L L.uniformContinuous)
      (bucSpatialCompositionConstant ‖L‖ k * A) := by
  exact hf.comp L L.uniformContinuous (BUC.const X L)
    (fun x ↦ L.hasFDerivAt) (BUCSpatialBound.const (k - 1) L)

namespace BUCSpatialRegularOn

/-- Applying a fixed continuous linear map preserves time-continuous BUC jets. -/
theorem postcompCLM {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) (L : F →L[ℝ] G) :
    BUCSpatialRegularOn s k (fun t ↦ BUC.postcompCLM L (f t)) := by
  induction k generalizing F G with
  | zero => exact (BUC.postcompCLM L).continuous.comp_continuousOn hf
  | succ k ih =>
    obtain ⟨hc, q, hq, hd⟩ := hf
    let J := ContinuousLinearMap.compL ℝ E F G L
    refine ⟨(BUC.postcompCLM L).continuous.comp_continuousOn hc,
      fun t ↦ BUC.postcompCLM J (q t), ih hq J, ?_⟩
    intro t ht x
    simpa only [BUC.postcompCLM_apply, J, ContinuousLinearMap.compL_apply] using!
      L.hasFDerivAt.comp x (hd t ht x)

/-- Fixed linear pullback preserves spatial regularity in the BUC norm in time. -/
theorem precompCLM {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) (L : X →L[ℝ] E) :
    BUCSpatialRegularOn s k (fun t ↦ (f t).comp L L.uniformContinuous) := by
  induction k generalizing F with
  | zero => exact (BUC.compCLM (𝕜 := ℝ) L L.uniformContinuous).continuous.comp_continuousOn hf
  | succ k ih =>
    obtain ⟨hc, q, hq, hd⟩ := hf
    let J := (ContinuousLinearMap.compL ℝ X E F).flip L
    refine ⟨(BUC.compCLM (𝕜 := ℝ) L L.uniformContinuous).continuous.comp_continuousOn hc,
      fun t ↦ BUC.postcompCLM J ((q t).comp L L.uniformContinuous),
      (ih hq).postcompCLM J, ?_⟩
    intro t ht x
    exact (hd t ht (L x)).comp x L.hasFDerivAt

end BUCSpatialRegularOn

end

end Planarwave
