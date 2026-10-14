/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontTrackingInitialSystem
import all Planarwave.Analysis.FrontTrackingExtension
import all Planarwave.Analysis.FrontTrackingBootstrapClosure

/-!
# Existence of the coupled tracking scheme on every finite physical slab

Following Proposition `tracking`, construct the phase and source one time
block at a time. The bootstrap closure supplies the old source bound needed
by each extension step. Since the extension only uses the preceding block,
there is no assumption of a future nonlinear source or a self-consistent
forcing before these have been constructed.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

/-- Every physical mild solution with sufficiently small initial
perturbation admits the self-consistent tracking scheme on the same finite
time interval. The smallness threshold is independent of that interval. -/
theorem exists_frontTrackingSystem :
    ∃ ε > 0, ∀ {T M : ℝ}
      (u : ℝ → BUC (ℝ^d) (ℝ^n))
      (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)),
      0 ≤ T → 0 ≤ M → M ≤ ε → ContinuousOn u (Icc 0 T) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u →
      ‖v₀‖ ≤ M →
      frontInverseModulatedPerturbation f D c φ h₂ hd (u 0) (c * 0) 0 = v₀ →
      ∃ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd T,
        X.u = u ∧ X.v₀ = v₀ := by
  obtain ⟨εe, hεe, hextend⟩ :=
    exists_frontTrackingSystem_extension f D c φ ψ h₁ h₂ h₃ hd
  obtain ⟨C, hC, εb, hεb, hclosed⟩ :=
    exists_front_tracking_bootstrap_closed f D c φ ψ h₁ h₂ h₃ hd
  refine ⟨min εe εb, lt_min hεe hεb, ?_⟩
  intro T M u v₀ hT hM hMε hu hm hv₀ hinitial
  have hMεe := hMε.trans (min_le_left _ _)
  have hMεb := hMε.trans (min_le_right _ _)
  have hbuild : ∀ k : ℕ, ∀ S : ℝ, 0 ≤ S → S ≤ (k : ℝ) →
      ContinuousOn u (Icc 0 S) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive S u →
      ∃ X : FrontTrackingSystem f D c φ ψ h₁ h₂ h₃ hd S,
        X.u = u ∧ X.v₀ = v₀ := by
    intro k
    induction k with
    | zero =>
        intro S hS hS0 huS hmS
        obtain ⟨X, hXu, hXv, _, _⟩ :=
          exists_frontTrackingInitialSystem f D c φ ψ h₁ h₂ h₃ hd hS
            (by norm_num at hS0; linarith) u huS hmS v₀ hinitial
        exact ⟨X, hXu, hXv⟩
    | succ k ih =>
        intro S hS hSk huS hmS
        by_cases hSk' : S ≤ (k : ℝ)
        · exact ih S hS hSk' huS hmS
        have hkS : (k : ℝ) ≤ S := (lt_of_not_ge hSk').le
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        obtain ⟨X, hXu, hXv⟩ := ih k hk le_rfl
          (huS.mono (Icc_subset_Icc le_rfl hkS)) (hmS.mono hkS)
        have hXvnorm : ‖X.v₀‖ ≤ M := by simpa only [hXv] using hv₀
        have hN : ∀ t ∈ Icc 0 (k : ℝ),
            ‖X.N t‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4) := by
          rcases hM.eq_or_lt with hzero | hpos
          · subst M
            have hXzero : X.v₀ = 0 := norm_le_zero_iff.mp hXvnorm
            intro t ht
            have hz := (X.vanish_of_initial_zero f D c φ ψ h₁ h₂ h₃ hd hXzero t ht).2.2
            simp only [hz, norm_zero, zero_mul, le_refl]
          · have hη := (hclosed X hpos hMεb hXvnorm k ⟨hk, le_rfl⟩).1
            exact fun t ht => (trackingBootstrapFunctional_le_one_bounds
              X.phase_regular.continuous X.source_continuous hpos ⟨hk, le_rfl⟩
              (hη.trans (by norm_num))).2 t ht |>.2
        obtain ⟨Y, hYu, hYv, _, _⟩ := hextend k S M X hkS
          (by simpa only [Nat.cast_add, Nat.cast_one] using hSk)
          hM hMεe hXvnorm hN (by simpa only [hXu] using huS)
          (by simpa only [hXu] using hmS)
        exact ⟨Y, hYu.trans hXu, hYv.trans hXv⟩
  obtain ⟨k, hk⟩ := exists_nat_ge T
  exact hbuild k T hT hk hu hm

end

end Planarwave
