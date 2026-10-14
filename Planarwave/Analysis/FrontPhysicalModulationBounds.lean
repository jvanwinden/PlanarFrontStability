/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontModulationHigherBounds
import all Planarwave.Analysis.MatrixReactionDiffusionRegularity
import Planarwave.Analysis.BUCLinearPullback

/-!
# Parabolic bounds for the actual inverse-modulated perturbation

Step 4 of the paper uses parabolic smoothing of the physical solution,
then the coordinate shear and interpolation. The physical Euclidean
space and the max-norm split space are not identified isometrically:
the bounded linear coordinate map carries its actual operator-norm cost.
Thus the high-order bound previously left as input to the modulation
estimate is now obtained from the original matrix mild equation.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ ψ : ℝ → ℝ^n)
  (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- All-order cutoff bounds for the actual physical perturbation.
No spatial derivative bound on the physical solution is assumed. -/
theorem exists_front_physical_modulated_cutoff_cn_bound
    (hd : 2 ≤ d) (k : ℕ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (u : ℝ → BUC (ℝ^d) (ℝ^n))
        (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
        (ξ σ : ℝ → BUC (ℝ^(d - 1)) ℝ),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ContinuousOn u (Icc 0 T) →
      (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u →
      ‖v₀‖ ≤ M → (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      (∀ t ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) →
      ∀ χ : ℝ → ℝ, (∀ t < δ, χ t = 0) → (∀ t, |χ t| ≤ 1) →
      ∀ t ∈ Icc 0 T, BUCSpatialBound k
        (χ t • frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)) C := by
  obtain ⟨A, hA, hpar⟩ := exists_matrixReactionDiffusion_cutoff_cn_bound
    (E := ℝ^d) f D h₁ k hδ hB
  let L := (coordinateEquiv hd).symm.toContinuousLinearMap
  let A' := bucSpatialCompositionConstant ‖L‖ k * A
  have hA' : 0 ≤ A' := mul_nonneg
    (zero_le_one.trans (one_le_bucSpatialCompositionConstant ‖L‖ k)) hA.le
  obtain ⟨C, hC, μ, hμ, hb⟩ := exists_front_modulated_cutoff_cn_bound
    (m := d - 1) f D c φ ψ h₁ h₂ h₃ k hA'
  refine ⟨C, hC, μ, hμ, ?_⟩
  intro T M u v₀ N ξ σ hT hM hMM hu hub hm hv₀ hN hξ hCH χ hχ₀ hχ t ht
  have hcut := hpar T hT u hu hub hm χ hχ₀ hχ t ht
  have hpull := hcut.precompCLM L
  have heq : (χ t • u t).comp L L.uniformContinuous =
      χ t • (u t).comp (coordinateEquiv hd).symm L.uniformContinuous := by
    ext x
    rfl
  rw [heq] at hpull
  exact hb T M v₀ N ξ σ hT hM hMM hv₀ hN hξ hCH t ht
    ((u t).comp (coordinateEquiv hd).symm L.uniformContinuous) (χ t) (hχ t) hpull

/-- The `3/4` second-derivative decay in Step 4 for the actual physical
perturbation, with its ninth-order input supplied by the parabolic PDE.
The remaining tracking estimate is explicitly the estimate on this same
physical perturbation, not on an unrelated Duhamel response. -/
theorem exists_front_physical_modulated_cutoff_c2_decay
    (hd : 2 ≤ d) {δ B K : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C > 0, ∃ M₀ > 0,
      ∀ (T M : ℝ) (u : ℝ → BUC (ℝ^d) (ℝ^n))
        (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
        (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
        (ξ σ : ℝ → BUC (ℝ^(d - 1)) ℝ),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ContinuousOn u (Icc 0 T) →
      (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u →
      ‖v₀‖ ≤ M → (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      IsForcedColeHopfMild (d_perp D φ ψ) (c / (2 * d_perp D φ ψ))
        (frontDelayedForcing f D c φ ψ h₃ v₀ N) ξ T →
      (∀ t ∈ Icc 0 T, coleHopfBUC (c / (2 * d_perp D φ ψ)) (σ t) = ξ t) →
      ∀ χ : ℝ → ℝ, (∀ t < δ, χ t = 0) → (∀ t, |χ t| ≤ 1) →
      ∀ t ∈ Icc 0 T,
        ‖frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)‖ ≤
          K * M / (1 + t) * Real.log (2 + t) →
        BUCSpatialBound 2
          (χ t • frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t))
          (C * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4)) := by
  obtain ⟨A, hA, μ, hμ, hhigh⟩ :=
    exists_front_physical_modulated_cutoff_cn_bound f D c φ ψ h₁ h₂ h₃ hd 9 hδ hB
  obtain ⟨C, hC, ε, hε, hi⟩ := exists_tracking_spatial_c2_bound
    (E := ℝ^(d - 1) × ℝ) (F := ℝ^n) hK hA.le
  refine ⟨C, hC, min μ ε, lt_min hμ hε, ?_⟩
  intro T M u v₀ N ξ σ hT hM hMM hu hub hm hv₀ hN hξ hCH χ hχ₀ hχ t ht hv
  have hh := hhigh T M u v₀ N ξ σ hT hM (hMM.trans (min_le_left _ _))
    hu hub hm hv₀ hN hξ hCH χ hχ₀ hχ t ht
  apply hi M t _ ⟨hM, hMM.trans (min_le_right _ _)⟩ ht.1 hh
  calc
    _ = |χ t| * ‖frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)‖ := by gcongr; exact hχ t
    _ ≤ _ := by simpa only [one_mul] using hv

end

end Planarwave
