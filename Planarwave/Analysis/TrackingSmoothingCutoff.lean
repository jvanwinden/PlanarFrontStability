/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # The smoothing cutoff in Step 4

The paper's cutoff is zero through time `1/8` and one from time `1/4`
onward, where the phase coefficients can first become nonzero.
-/

namespace Planarwave

noncomputable section

def trackingSmoothingCutoff (t : ℝ) : ℝ := Real.smoothTransition (8 * t - 1)

theorem trackingSmoothingCutoff_zero {t : ℝ} (ht : t ≤ 1 / 8) :
    trackingSmoothingCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem trackingSmoothingCutoff_one {t : ℝ} (ht : 1 / 4 ≤ t) :
    trackingSmoothingCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem abs_trackingSmoothingCutoff_le_one (t : ℝ) : |trackingSmoothingCutoff t| ≤ 1 := by
  unfold trackingSmoothingCutoff
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem contDiff_trackingSmoothingCutoff : ContDiff ℝ (⊤ : ℕ∞) trackingSmoothingCutoff :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

end

end Planarwave
