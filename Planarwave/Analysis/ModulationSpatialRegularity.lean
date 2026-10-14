/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ModulationContinuity
public import Planarwave.Analysis.ModulationHigherBounds
public import Planarwave.Analysis.BUCLinearPullback

@[expose] public section

/-!
# Time-continuous spatial BUC jets under modulation

Inverse modulation preserves the hierarchy of genuine spatial derivatives
which are continuous in the BUC norm in time. The zeroth-order step uses
uniform continuity of the data, so the construction does not require an
extra derivative. The higher-order steps use the actual spatial chain rule.
-/

namespace Planarwave

noncomputable section

universe u

variable {Y : Type} {F : Type u}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace BUCSpatialRegularOn

/-- A field constant in both time and space has time-continuous spatial jets
of every finite order. -/
theorem const (s : Set ℝ) (k : ℕ) (v : F) :
    BUCSpatialRegularOn s k (fun _ ↦ BUC.const Y v) := by
  cases k with
  | zero => exact continuousOn_const
  | succ k =>
    refine ⟨continuousOn_const, fun _ ↦ 0, zero s k, ?_⟩
    intro t ht x
    simpa only [BUC.const_apply, BUC.zero_apply] using!
      hasFDerivAt_const (𝕜 := ℝ) v x

/-- The shear derivative inherits the phase derivative's time-continuous BUC
jets. The translation plays no role in this spatial derivative. -/
theorem modulationDerivative {s : Set ℝ} {k : ℕ}
    {q : ℝ → BUC Y (Y →L[ℝ] ℝ)} (hq : BUCSpatialRegularOn s k q) :
    BUCSpatialRegularOn s k (fun t ↦ modulationDerivativeBUC (q t)) := by
  have hc := const (Y := Y × ℝ) s k (ContinuousLinearMap.id ℝ (Y × ℝ))
  have hp := (hq.precompCLM (ContinuousLinearMap.fst ℝ Y ℝ)).postcompCLM
    modulationDerivativeLift
  exact hc.add hp

/-- Moving modulation coordinates preserve all finite-order time-continuous
spatial jets, using the genuine Fréchet chain rule. -/
theorem modulationShift {s : Set ℝ} {k : ℕ}
    {u : ℝ → BUC (Y × ℝ) F} {σ : ℝ → BUC Y ℝ} {a : ℝ → ℝ}
    (hu : BUCSpatialRegularOn s k u) (hσ : BUCSpatialRegularOn s k σ)
    (ha : ContinuousOn a s) :
    BUCSpatialRegularOn s k (fun t ↦ Planarwave.modulationShift (a t) (σ t) (u t)) := by
  induction k generalizing F with
  | zero => exact continuousOn_modulationShift ha hσ hu
  | succ k ih =>
    have hσk := hσ.of_succ
    obtain ⟨huc, qu, hqu, hdu⟩ := hu
    obtain ⟨hσc, qσ, hqσ, hdσ⟩ := hσ
    let J := ContinuousLinearMap.compL ℝ (Y × ℝ) (Y × ℝ) F
    have hq := (ih hqu hσk).bilinear hqσ.modulationDerivative J
    refine ⟨continuousOn_modulationShift ha hσc huc,
      fun t ↦ BUC.bilinearBUC J (Planarwave.modulationShift (a t) (σ t) (qu t))
        (modulationDerivativeBUC (qσ t)), hq, ?_⟩
    intro t ht x
    simpa only [BUC.bilinearBUC_apply, J, ContinuousLinearMap.compL_apply] using!
      (hdu t ht (modulationCoordinates (a t) (σ t) x)).comp x
        (hasFDerivAt_modulationCoordinates (a t) (σ t) (qσ t) (hdσ t ht) x)

end BUCSpatialRegularOn

end

end Planarwave
