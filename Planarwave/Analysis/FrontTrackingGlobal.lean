/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingExistence
import all Planarwave.Analysis.FrontTrackingBootstrapClosure
import all Planarwave.Analysis.MatrixReactionDiffusionGlobal

/-!
# Global physical solutions from the closed tracking bounds

The finite-slab causal construction and the closed nonlinear bootstrap bound
the physical solution throughout its maximal lifetime. The physical norm is
independent of the modulation shear, and the logarithmic tracking weight is
bounded by one. The continuation theorem therefore makes the lifetime infinite.
Every finite slab retains an actual self-consistent tracking system and the
paper's phase, perturbation, and nonlinear-source estimates.
-/

open Set
open scoped ENNReal

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- Small BUC perturbations of the front give global physical classical
solutions. Every finite slab admits a coupled tracking system with the closed
estimates, without any additional source bootstrap or existence hypothesis. -/
theorem exists_front_global_solution_with_tracking :
    ∃ C > 0, ∃ ε > 0,
      ∀ (u₀ : BUC (ℝ^d) (ℝ^n)) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) (M : ℝ),
      0 ≤ M → M ≤ ε → ‖v₀‖ ≤ M →
      frontInverseModulatedPerturbation f D c φ h₂ hd u₀ (c * 0) 0 = v₀ →
      ∃ u : ℝ → BUC (ℝ^d) (ℝ^n),
        u 0 = u₀ ∧ IsRDESolution f D (fun t x ↦ u t x) ∧
        (∀ t, 0 ≤ t → ‖u t‖ ≤ C * M + ‖frontSplitProfileBUC (m := d - 1) f D c φ h₂‖) ∧
        ∀ T : ℝ, 0 ≤ T → ∃ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T,
          X.u = u ∧ X.v₀ = v₀ ∧
          ∀ t ∈ Icc 0 T,
            ‖X.σ t‖ ≤ C * M ∧
            ‖X.perturbation t‖ ≤ C * M / (1 + t) * Real.log (2 + t) ∧
            ‖X.N t‖ ≤ C * M ^ ((7 : ℝ) / 4) * (1 + t) ^ (-(5 : ℝ) / 4) := by
  obtain ⟨C, hC, εb, hεb, hb⟩ :=
    exists_front_tracking_unconditional_bounds f D c φ ψ h₁ h₂ h₃ hd
  obtain ⟨εe, hεe, hex⟩ := exists_frontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd
  refine ⟨C, hC, min εb εe, lt_min hεb hεe, ?_⟩
  intro u₀ v₀ M hM hMε hv₀ hinit
  have hMb : M ≤ εb := hMε.trans (min_le_left _ _)
  have hMe : M ≤ εe := hMε.trans (min_le_right _ _)
  obtain ⟨τ, u, hm⟩ := exists_maximal_matrixReactionDiffusion f D h₁ u₀
  have hexbelow : ∀ T : ℝ, 0 ≤ T → ENNReal.ofReal T < τ →
      ∃ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T, X.u = u ∧ X.v₀ = v₀ := by
    intro T hT hTτ
    apply hex u v₀ hT hM hMe (hm.continuousOn_Icc hTτ) (hm.mild T hT hTτ) hv₀
    simpa only [hm.initial] using hinit
  have hphysical : ∀ t, 0 ≤ t → ENNReal.ofReal t < τ →
      ‖u t‖ ≤ C * M + ‖frontSplitProfileBUC (m := d - 1) f D c φ h₂‖ := by
    intro t ht htτ
    obtain ⟨X, hXu, hXv₀⟩ := hexbelow t ht htτ
    have hXt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
    have hv := (hb X hM hMb (by simpa only [hXv₀] using hv₀) t hXt).2.1
    have hlog : Real.log (2 + t) ≤ 1 + t := by
      have := Real.log_le_sub_one_of_pos (show 0 < 2 + t by linarith)
      linarith
    have hvsmall : ‖X.perturbation t‖ ≤ C * M := hv.trans (by
      calc
        C * M / (1 + t) * Real.log (2 + t) ≤ C * M / (1 + t) * (1 + t) :=
          mul_le_mul_of_nonneg_left hlog (div_nonneg (mul_nonneg hC.le hM) (by linarith))
        _ = C * M := div_mul_cancel₀ _ (by linarith))
    have hu := norm_le_frontInverseModulatedPerturbation_add_profile f D c φ h₂ hd
      (X.u t) (c * t) (X.σ t)
    change ‖X.u t‖ ≤ ‖X.perturbation t‖ + _ at hu
    rw [hXu] at hu
    exact hu.trans (add_le_add hvsmall le_rfl)
  have hτ : τ = ⊤ := hm.lifetime_eq_top_of_bounded (by positivity) hphysical
  have hfinite (t : ℝ) : ENNReal.ofReal t < τ := by
    rw [hτ]
    exact ENNReal.ofReal_lt_top
  refine ⟨u, hm.initial, hm.isRDESolution_of_lifetime_top hτ,
    fun t ht ↦ hphysical t ht (hfinite t), ?_⟩
  intro T hT
  obtain ⟨X, hXu, hXv₀⟩ := hexbelow T hT (hfinite T)
  exact ⟨X, hXu, hXv₀, hb X hM hMb (by simpa only [hXv₀] using hv₀)⟩

end

end Planarwave
