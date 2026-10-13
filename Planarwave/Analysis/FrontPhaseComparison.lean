/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing
import all Planarwave.Analysis.ChallengePhaseEvolution
import Planarwave.Analysis.ForcedPhaseComparison

/-!
# The phase comparison for the actual front

Specialize the final Cole--Hopf argument to the original transverse
diffusivity, the actual adjoint projection, and the causal front forcing.
Identify its unforced datum with the initial phase in `Challenge.lean`.
-/

open MeasureTheory Set
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The constants are chosen before the perturbation and source. The
improved forcing bound is supplied by `FrontImprovedForcingDecay` once the
nonlinear tracking estimates have been established. -/
theorem exists_front_forcedPhase_comparison_bound {K G : ℝ} (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C > 0, ∃ ε > 0, ∀ (T M : ℝ) (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
      (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (ξ σ : ℝ → BUC (ℝ^m) ℝ),
      M ∈ Icc 0 ε → ‖v₀‖ ≤ M →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      (∀ r ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ r) = ξ r) →
      (∀ r ∈ Icc 0 T, ‖ξ r‖ ≤ K * M) →
      (∀ r ∈ Icc 0 T, ‖frontDelayedForcing f D c φ ψ h₃ v₀ N r‖ ≤ G *
        (trackingCutoff r * M + M ^ 2 * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r))) →
      ∀ t ∈ Icc 0 T,
        ‖σ t - coleHopfEvolution (d_perp D φ ψ) (c / (2 * d_perp D φ ψ)) t
          (-longitudinalPairing ψ h₃.integrable v₀)‖ ≤ C * (M ^ 2 + M / (1 + t)) := by
  have hP : 0 ≤ ∫ z, ‖ψ z‖ := integral_nonneg fun z ↦ norm_nonneg (ψ z)
  obtain ⟨C, hC, ε, hε, hb⟩ := exists_delayed_forcedPhase_comparison_bound
    (E := ℝ^m) (c / (2 * d_perp D φ ψ)) hP hK hG
  refine ⟨C, hC, ε, hε, ?_⟩
  intro T M v₀ N ξ σ hM hv₀ hξ htransform hξbound hgbound
  exact hb (longitudinalPairing ψ h₃.integrable v₀)
    (fun r ↦ longitudinalPairing ψ h₃.integrable (N r)) ξ σ
    h₃.transverse_low_wavenumber.le hM
    ((norm_longitudinalPairing_le ψ h₃.integrable v₀).trans
      (mul_le_mul_of_nonneg_left hv₀ hP)) hξ htransform hξbound hgbound

/-- The sign of the datum in the comparison is exactly the sign in the
challenge: the unforced phase starts at the negative projection of `u₀-φ`. -/
theorem initialPhaseBUC_eq_neg_longitudinalPairing
    (hd : 2 ≤ d) (h₂ : IsSmoothFront f D c φ) (u₀ : BUC (ℝ^d) (ℝ^n)) :
    initialPhaseBUC f D c φ ψ hd h₂ h₃ (isBUC_coe u₀) =
      -longitudinalPairing ψ h₃.integrable
        (frontInverseModulatedPerturbation f D c φ h₂ hd u₀ 0 0) := by
  ext y
  simp only [initialPhaseBUC_apply, BUC.neg_apply, longitudinalPairing_apply,
    frontInverseModulatedPerturbation_apply, BUC.zero_apply, add_zero, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← inner_neg_right, neg_sub]

end

end Planarwave
