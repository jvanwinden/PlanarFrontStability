/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import Planarwave.Analysis.ForcedPhaseClassical
import Planarwave.Analysis.ForcedColeHopfRegularity
import Planarwave.Analysis.ForcedColeHopfBounds
import Planarwave.Analysis.BUCBilinear
import Planarwave.Analysis.ColeHopfInverseDerivative
import Planarwave.Analysis.DelayedHeatForcingFirstDerivativeBounds

/-!
# The first derivative field of the front's delayed forcing

Specialize the delayed forcing's BUC derivative field to the original
transverse diffusivity and adjoint-projected source. This is the derivative
field used in the subsequent phase estimates.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The genuine first derivative of the front's delayed forcing. -/
def frontDelayedForcingFDeriv (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) : ℝ → BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ) :=
  delayedHeatForcingFDeriv h₃.transverse_low_wavenumber (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))

end

end Planarwave
