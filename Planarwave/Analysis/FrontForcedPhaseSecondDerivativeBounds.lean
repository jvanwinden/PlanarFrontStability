/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import all Planarwave.Analysis.FrontForcedPhaseFirstDerivativeBounds
import Planarwave.Analysis.ForcedPhaseClassical
import Planarwave.Analysis.ColeHopfInverseSecondDerivative
import Planarwave.Analysis.DelayedHeatForcingSecondDerivativeBounds

/-!
# Second-order phase estimates for the actual front

Specialize the C² Cole--Hopf estimate and the actual phase Laplacian
to the original diffusivity and adjoint-projected delayed forcing.
The forcing block estimate uses only undifferentiated nonlinear data.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance frontC2TensorNormedAddCommGroup :
    NormedAddCommGroup (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) := inferInstance
local instance frontC2TensorNormedSpace : NormedSpace ℝ (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) := inferInstance
local instance frontC2BUCNormedAddCommGroup :
    NormedAddCommGroup (BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ)) := inferInstance

/-- The genuine Hessian of the front's delayed forcing. -/
def frontDelayedForcingFDeriv2 (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ) :=
  delayedHeatForcingFDeriv2 h₃.transverse_low_wavenumber (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))


end

end Planarwave
