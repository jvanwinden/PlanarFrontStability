/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontDelayedForcing

/-!
# Causal extension of the tracking forcing

For the unit-block construction of Proposition `tracking`, a source known on
`[0,k]` determines the forcing on the whole interval `[0,k+1]`. Extending
that source by zero allows the already proved forced-phase existence theorem
to be used on the next block without assuming future nonlinear estimates.
-/

open Set

namespace Planarwave

noncomputable section

section Generic

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Equality of the old source determines every forcing value through the
end of the next unit block, not only the value at its right endpoint. -/
theorem delayedHeatForcing_eqOn_of_past (a : ℝ) (p : BUC E F)
    {N Q : ℝ → BUC E F} (k : ℕ) (h : EqOn N Q (Icc 0 (k : ℝ))) :
    EqOn (delayedHeatForcing a p N) (delayedHeatForcing a p Q)
      (Iic ((k : ℝ) + 1)) := by
  intro t ht
  have ht' : t ≤ (k : ℝ) + 1 := ht
  simp only [delayedHeatForcing]
  congr 1
  apply tsum_congr
  intro j
  by_cases hj : (j : ℝ) + 1 ≤ k
  · rw [delayedHeatBlock_congr a j (fun r hr ↦
      h ⟨(Nat.cast_nonneg j).trans hr.1, hr.2.trans hj⟩)]
  · have hkj : k ≤ j := by
      by_contra hbad
      have hlt : j < k := Nat.lt_of_not_ge hbad
      exact hj (by exact_mod_cast hlt)
    have hcast : (k : ℝ) ≤ j := by exact_mod_cast hkj
    have hz : trackingCutoff (t - ((j : ℝ) + 1)) = 0 :=
      trackingCutoff_eq_zero_of_le (by linarith)
    simp only [hz, zero_smul]

end Generic

section PastSource

variable {F : Type*} [NormedAddCommGroup F]

/-- An auxiliary extension used only to compute the next forcing block.
No continuity of this extension at the block boundary is needed. -/
def trackingPastSource (N : ℝ → F) (k : ℕ) (t : ℝ) : F :=
  if t ≤ (k : ℝ) then N t else 0

theorem trackingPastSource_eqOn (N : ℝ → F) (k : ℕ) :
    EqOn (trackingPastSource N k) N (Icc 0 (k : ℝ)) := by
  intro t ht
  exact if_pos ht.2

/-- The source bootstrap extends to all future times for the auxiliary
source. It is not an assertion about the as-yet unconstructed true source. -/
theorem norm_trackingPastSource_le {N : ℝ → F} {k : ℕ} {M γ : ℝ}
    (hM : 0 ≤ M) (hN : ∀ r ∈ Icc 0 (k : ℝ), ‖N r‖ ≤ M * (1 + r) ^ (-γ))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖trackingPastSource N k t‖ ≤ M * (1 + t) ^ (-γ) := by
  unfold trackingPastSource
  split_ifs with hk
  · exact hN t ⟨ht, hk⟩
  · simpa only [norm_zero] using mul_nonneg hM (Real.rpow_nonneg (by linarith) _)

end PastSource

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

theorem frontDelayedForcing_eqOn_of_past (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    {N Q : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)} (k : ℕ) (h : EqOn N Q (Icc 0 (k : ℝ))) :
    EqOn (frontDelayedForcing f D c φ ψ h₃ v₀ N)
      (frontDelayedForcing f D c φ ψ h₃ v₀ Q) (Iic ((k : ℝ) + 1)) :=
  delayedHeatForcing_eqOn_of_past _ _ k (fun _ hr ↦ congrArg _ (h hr))

theorem frontDelayedForcing_trackingPastSource (v₀ : BUC (ℝ^m × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (k : ℕ) :
    EqOn (frontDelayedForcing f D c φ ψ h₃ v₀ (trackingPastSource N k))
      (frontDelayedForcing f D c φ ψ h₃ v₀ N) (Iic ((k : ℝ) + 1)) :=
  frontDelayedForcing_eqOn_of_past f D c φ ψ h₃ v₀ k (trackingPastSource_eqOn N k)

end

end Planarwave
