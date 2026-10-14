/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearity
import Planarwave.Analysis.InverseModulationNonlinearityContinuity
import Planarwave.Analysis.BUCPartialDerivativeContinuity

/-!
# Continuity of the actual front's nonlinear source

The source in the delayed tracking construction extends continuously to the
rough initial BUC data. Spatial derivatives are required to be continuous only
at positive times, because their coefficients vanish on the initial interval.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)

local instance : NormedAddCommGroup (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ) (E := (ℝ^m × ℝ) →L[ℝ] ℝ^n)
local instance : NormedAddCommGroup
    (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ)
    (E := (ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)

/-- No spatial derivatives enter the remainder before the phase is switched on. -/
theorem frontInverseModulationNonlinearity_zero_phase
    (v : BUC (ℝ^m × ℝ) (ℝ^n))
    (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)) :
    frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ 0 0 0 =
      BUC.reactionRemainder f
        (h₁.smooth.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
        (frontSplitProfileBUC f D c φ h₂) v :=
  inverseModulationNonlinearity_zero_phase f _ D c _ _ v _ _ _

/-- Norm continuity of the concrete front remainder on a positive-time slab. -/
theorem continuousOn_frontInverseModulationNonlinearity {I : Set ℝ}
    {v : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)}
    {v₁ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n)}
    {v₂ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)}
    {s : ℝ → BUC (ℝ^m) (ℝ^m)} {l g : ℝ → BUC (ℝ^m) ℝ}
    (hv : ContinuousOn v I) (hv₁ : ContinuousOn v₁ I) (hv₂ : ContinuousOn v₂ I)
    (hs : ContinuousOn s I) (hl : ContinuousOn l I) (hg : ContinuousOn g I) :
    ContinuousOn (fun t ↦ frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
      (v t) (v₁ t) (v₂ t) (s t) (l t) (g t)) I := by
  have hfirst := BUC.continuous_longitudinalDerivativeField.comp_continuousOn hv₁
  have hsecond := BUC.continuous_longitudinalSecondDerivativeField.comp_continuousOn hv₂
  have hmixed := BUC.continuous_mixedDerivativeField.comp_continuousOn hv₂
  simpa only [frontInverseModulationNonlinearity] using!
    continuousOn_inverseModulationNonlinearity f
      (h₁.smooth.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      D c (d_perp D φ ψ) (frontSplitProfileBUC f D c φ h₂)
      hv hfirst hsecond hmixed hs hl hg

/-- Initial zero phase coefficients give continuity all the way to rough initial
data; the derivative fields need not have limits at time zero. -/
theorem continuousOn_frontInverseModulationNonlinearity_of_initial_zero
    {T δ : ℝ} (hδ : 0 < δ)
    {v : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)}
    {v₁ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n)}
    {v₂ : ℝ → BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)}
    {s : ℝ → BUC (ℝ^m) (ℝ^m)} {l g : ℝ → BUC (ℝ^m) ℝ}
    (hv : ContinuousOn v (Icc 0 T))
    (hv₁ : ContinuousOn v₁ (Ioc 0 T)) (hv₂ : ContinuousOn v₂ (Ioc 0 T))
    (hs : ContinuousOn s (Ioc 0 T)) (hl : ContinuousOn l (Ioc 0 T))
    (hg : ContinuousOn g (Ioc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < δ → s t = 0 ∧ l t = 0 ∧ g t = 0) :
    ContinuousOn (fun t ↦ frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
      (v t) (v₁ t) (v₂ t) (s t) (l t) (g t)) (Icc 0 T) := by
  have hfirst := BUC.continuous_longitudinalDerivativeField.comp_continuousOn hv₁
  have hsecond := BUC.continuous_longitudinalSecondDerivativeField.comp_continuousOn hv₂
  have hmixed := BUC.continuous_mixedDerivativeField.comp_continuousOn hv₂
  simpa only [frontInverseModulationNonlinearity] using!
    continuousOn_inverseModulationNonlinearity_of_initial_zero f
      (h₁.smooth.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      D c (d_perp D φ ψ) (frontSplitProfileBUC f D c φ h₂) hδ
      hv hfirst hsecond hmixed hs hl hg hzero

end

end Planarwave
