/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import Planarwave.Analysis.ForcedColeHopfExistence

/-!
# The initial zero interval in the actual tracking scheme

The delayed forcing and forced phase vanish through time `1/4`. Hence all
coefficients of perturbation derivatives in the nonlinear source vanish
there, which permits rough initial BUC perturbations.
-/

open Set
open scoped Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The actual forcing vanishes before its first pulse. -/
theorem frontDelayedForcing_initial_zero
    (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
    {t : ℝ} (ht : t ≤ 1 / 4) : frontDelayedForcing f D c φ ψ h₃ v₀ N t = 0 :=
  delayedHeatForcing_eq_zero_of_le_quarter _ _ _ ht

/-- The inverse Cole--Hopf phase is zero on the same initial interval. -/
theorem frontForcedPhase_initial_zero
    {T t : ℝ} {v₀ : BUC (ℝ^m × ℝ) (ℝ^n)} {N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)}
    {ξ σ : ℝ → BUC (ℝ^m) ℝ}
    (hξ : IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
      (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T)
    (ht : t ∈ Icc 0 T) (hquarter : t ≤ 1 / 4)
    (hCH : coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) : σ t = 0 := by
  have hξt : ξ t = 0 := hξ.delayed_initial_zero ht hquarter
  ext y
  apply (strictMono_coleHopf (c / (2 * d_perp D φ ψ))).injective
  have heq := congrArg (fun w : BUC (ℝ^m) ℝ ↦ w y) (hCH.trans hξt)
  simpa only [coleHopfBUC_apply, BUC.zero_apply, coleHopf_zero_apply] using heq

/-- In particular every coefficient multiplying a perturbation derivative
in the nonlinear source vanishes on the initial quarter interval. -/
theorem frontTrackingCoefficients_initial_zero
    {T t : ℝ} {v₀ : BUC (ℝ^m × ℝ) (ℝ^n)} {N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)}
    {ξ σ : ℝ → BUC (ℝ^m) ℝ}
    (hξ : IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
      (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T)
    (ht : t ∈ Icc 0 T) (hquarter : t ≤ 1 / 4)
    (hCH : coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t)
    (s : BUC (ℝ^m) (ℝ^m)) (l : BUC (ℝ^m) ℝ)
    (hs : ∀ y, s y = ∇ (σ t : ℝ^m → ℝ) y)
    (hl : ∀ y, l y = Δ (σ t : ℝ^m → ℝ) y) :
    s = 0 ∧ l = 0 ∧ frontDelayedForcing f D c φ ψ h₃ v₀ N t = 0 := by
  have hσt := frontForcedPhase_initial_zero f D c φ ψ h₃ hξ ht hquarter hCH
  refine ⟨?_, ?_, frontDelayedForcing_initial_zero f D c φ ψ h₃ v₀ N hquarter⟩
  · apply BUC.ext
    intro y
    rw [hs y, hσt]
    change ∇ (fun _ : ℝ^m ↦ (0 : ℝ)) y = 0
    exact gradient_fun_const y 0
  · apply BUC.ext
    intro y
    rw [hl y, hσt]
    change Δ (fun _ : ℝ^m ↦ (0 : ℝ)) y = 0
    simp

end

end Planarwave
