/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCPartialDerivatives

@[expose] public section

/-! # Norm continuity of extracted partial derivative fields -/

namespace BUC

noncomputable section

variable {Y F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : NormedAddCommGroup (BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := (Y × ℝ) →L[ℝ] F)
local instance : NormedAddCommGroup (BUC (Y × ℝ) ((Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := (Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F)
local instance : NormedAddCommGroup (BUC (Y × ℝ) (Y →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := Y →L[ℝ] F)

/-- Extracting the longitudinal derivative is continuous in the jet norm. -/
theorem continuous_longitudinalDerivativeField :
    Continuous (longitudinalDerivativeField (Y := Y) (F := F)) :=
  (postcompCLM (ContinuousLinearMap.apply ℝ F ((0 : Y), (1 : ℝ)))).continuous

/-- The second longitudinal derivative depends continuously on the full Hessian field. -/
theorem continuous_longitudinalSecondDerivativeField :
    Continuous (longitudinalSecondDerivativeField (Y := Y) (F := F)) :=
  continuous_longitudinalDerivativeField.comp
    (continuous_longitudinalDerivativeField (F := (Y × ℝ) →L[ℝ] F))

/-- The mixed transverse/longitudinal derivative depends continuously on the full Hessian. -/
theorem continuous_mixedDerivativeField :
    Continuous (mixedDerivativeField (Y := Y) (F := F)) := by
  simpa only [mixedDerivativeField] using!
    (postcompCLM (𝕜 := ℝ) (E := (Y × ℝ) →L[ℝ] (Y × ℝ) →L[ℝ] F) (F := Y →L[ℝ] F)
    ((ContinuousLinearMap.precomp F (ContinuousLinearMap.inl ℝ Y ℝ)).comp
      ((ContinuousLinearMap.apply ℝ F ((0 : Y), (1 : ℝ))).postcomp (Y × ℝ)))).continuous

end

end BUC
