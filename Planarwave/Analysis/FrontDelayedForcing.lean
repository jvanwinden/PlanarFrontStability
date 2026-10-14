/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontProjectedNonlinearity
import Planarwave.Analysis.DelayedHeatForcingSmoothing
import Planarwave.Analysis.DelayedHeatForcingRegularity

/-!
# Delayed forcing for the actual front

Specialize `eq:defgnew` to the original transverse diffusivity and adjoint
projection, and prove continuity of the resulting forcing path. The source
is supplied as input; later tracking estimates specialize it to the
inverse-modulation nonlinearity and bound the forcing.
-/

open MeasureTheory Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The front forcing, with initial perturbation `v₀` and nonlinear source `N`. -/
def frontDelayedForcing (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) :
    ℝ → BUC (ℝ^m) ℝ :=
  delayedHeatForcing (d_perp D φ ψ) (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r))

theorem continuous_frontDelayedForcing (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) :
    Continuous (frontDelayedForcing f D c φ ψ h₃ v₀ N) :=
  continuous_delayedHeatForcing _ _ _

end

end Planarwave
