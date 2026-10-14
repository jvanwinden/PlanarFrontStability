/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialComposition
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# Higher BUC bounds along a bounded autonomous ODE trajectory

On the compact closure of the state range, each smooth observable and
its derivative along the vector field is bounded and uniformly continuous.
Iterating this observation constructs genuine BUC derivatives of every
finite order. It will be applied to the traveling-wave phase-space ODE.
-/

open scoped ContDiff

namespace Planarwave

noncomputable section

universe u

variable {V : Type} {F : Type u}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth observables of a bounded autonomous trajectory have all-order
bounded uniformly continuous spatial derivatives. -/
theorem exists_bucSpatialBound_observable_of_ode (u : BUC ℝ V)
    (R : V → V) (hR : ContDiff ℝ ∞ R)
    (hd : ∀ z, HasDerivAt u (R (u z)) z)
    (k : ℕ) (G : V → F) (hG : ContDiff ℝ ∞ G) :
    ∃ A ≥ 0, BUCSpatialBound k (BUC.postcompContinuous G hG.continuous u) A := by
  induction k generalizing F with
  | zero => exact ⟨‖BUC.postcompContinuous G hG.continuous u‖, norm_nonneg _, le_rfl⟩
  | succ k ih =>
    let L := (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toContinuousLinearEquiv.toContinuousLinearMap
    let H : V → (ℝ →L[ℝ] F) := fun v ↦ L (fderiv ℝ G v (R v))
    have hH : ContDiff ℝ ∞ H :=
      L.contDiff.comp ((hG.fderiv_right (by simp)).clm_apply hR)
    obtain ⟨A, hA, hb⟩ := ih H hH
    refine ⟨max ‖BUC.postcompContinuous G hG.continuous u‖ A, le_trans hA (le_max_right _ _),
      le_max_left _ _, BUC.postcompContinuous H hH.continuous u,
      hb.mono (le_max_right _ _), ?_⟩
    intro z
    change HasFDerivAt (G ∘ u)
      (ContinuousLinearMap.toSpanSingleton ℝ (fderiv ℝ G (u z) (R (u z)))) z
    exact ((hG.differentiable (by simp) (u z)).hasFDerivAt.comp_hasDerivAt z (hd z)).hasFDerivAt

/-- In particular, every spatial derivative of the trajectory itself is BUC. -/
theorem exists_bucSpatialBound_of_ode (u : BUC ℝ V)
    (R : V → V) (hR : ContDiff ℝ ∞ R)
    (hd : ∀ z, HasDerivAt u (R (u z)) z) (k : ℕ) :
    ∃ A > 0, BUCSpatialBound k u A := by
  obtain ⟨A, _, hA⟩ := exists_bucSpatialBound_observable_of_ode u R hR hd k id contDiff_id
  have heq : BUC.postcompContinuous id (continuous_id : Continuous (id : V → V)) u = u :=
    BUC.ext fun _ ↦ rfl
  rw [heq] at hA
  exact ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hA.mono (le_max_left _ _)⟩

end

end Planarwave
