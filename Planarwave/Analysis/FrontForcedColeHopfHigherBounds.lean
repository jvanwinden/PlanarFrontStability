/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontForcingHigherDerivativeBounds
import Planarwave.Analysis.ForcedColeHopfHigherBounds

/-!
# The actual front's uniform all-order Cole--Hopf bound

This supplies `eq:xiestC9` in Step 1 of `lem:key`, and its finite-order
generalization, from the original adjoint projection and the unprojected
source bootstrap. It constructs the Cole--Hopf solution with genuine BUC
derivative paths. Transfer of the quantitative bound to the inverse phase
and construction of the coupled tracking solution remain separate tasks.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- Uniform `C^k` bounds for the actual front's Cole--Hopf variable.
All constants are chosen before the horizon, data, source, and solution. -/
theorem exists_front_forcedColeHopf_cn_bound (k : ℕ) :
    ∃ C > 0, ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
      (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (ξ : ℝ → BUC (ℝ^m) ℝ),
      0 ≤ T → 0 ≤ M → M ≤ 1 → ‖v₀‖ ≤ M →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      ∀ t ∈ Icc 0 T, BUCSpatialBound k (ξ t) (C * M) := by
  obtain ⟨C, hC, hg⟩ := exists_frontDelayedForcing_cn_decay (m := m) f D c φ ψ h₃ k
    (by norm_num : (0 : ℝ) ≤ 5 / 4)
  refine ⟨4 * C * Real.exp (4 * (|c / (2 * d_perp D φ ψ)| * 2 ^ k) * C), by positivity, ?_⟩
  intro T M v₀ N ξ hT hM hM1 hv₀ hN hξ t ht
  have hgreg : BUCSpatialRegularOn (Icc 0 T) k (frontDelayedForcing f D c φ ψ h₃ v₀ N) :=
    bucSpatialRegularOn_delayedHeatForcing k h₃.transverse_low_wavenumber
      (longitudinalPairing ψ h₃.integrable v₀)
      (fun r ↦ longitudinalPairing ψ h₃.integrable (N r)) T
  apply hξ.spatial_bound hT hC.le hM hM1 k hgreg _ ht
  intro r hr
  apply hgreg.bound_of_iteratedFDeriv hr
  intro j hj x
  obtain ⟨q, hq, hqn⟩ := hg T M v₀ N hM hv₀ (by simpa only [neg_div] using hN) r hr j hj
  rw [← hq x]
  simpa only [neg_div] using (q.norm_apply_le x).trans hqn

end

end Planarwave
