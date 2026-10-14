/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Interpolation for bounded uniformly continuous derivatives

The elementary estimate `‖f'‖ ≤ (2 / ε) * ‖f‖ + ε * ‖f''‖` permits absorption of the
first-order drift into the second-order diffusion. It supplies the graph-norm estimate needed
to identify the longitudinal generator domain in the semigroup construction of Section 2.
-/

open Set

namespace BUC

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Banach-valued interpolation estimate with arbitrarily small second-derivative coefficient. -/
theorem norm_deriv_le_of_hasDerivAt (f g h : BUC ℝ F)
    (hfg : ∀ x, HasDerivAt f (g x) x) (hgh : ∀ x, HasDerivAt g (h x) x)
    {ε : ℝ} (hε : 0 < ε) : ‖g‖ ≤ (2 / ε) * ‖f‖ + ε * ‖h‖ := by
  apply norm_le (by positivity) |>.mpr
  intro x
  have hg (y : ℝ) (hy : y ∈ Icc x (x + ε)) : ‖g y - g x‖ ≤ ‖h‖ * ε := by
    have hm := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun z (_ : z ∈ Icc x (x + ε)) ↦ (hgh z).hasDerivWithinAt)
      (fun z (_ : z ∈ Ico x (x + ε)) ↦ h.norm_apply_le z) y hy
    exact hm.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) (norm_nonneg h))
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ ↦ f z - (z - x) • g x) (g y - g x) y := by
    simpa only [one_smul] using!
      (hfg y).sub (((hasDerivAt_id y).sub_const x).smul_const (g x))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y (_ : y ∈ Icc x (x + ε)) ↦ (hd y).hasDerivWithinAt)
    (fun y (hy : y ∈ Ico x (x + ε)) ↦ hg y ⟨hy.1, hy.2.le⟩)
    (x + ε) (show x + ε ∈ Icc x (x + ε) from ⟨by linarith, le_rfl⟩)
  simp only [add_sub_cancel_left, sub_self, zero_smul, sub_zero] at hm
  have hbound : ε * ‖g x‖ ≤ 2 * ‖f‖ + ‖h‖ * ε * ε := by
    calc
      ε * ‖g x‖ = ‖ε • g x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      _ = ‖(f (x + ε) - f x) - (f (x + ε) - ε • g x - f x)‖ := by
        congr 1
        abel
      _ ≤ ‖f (x + ε) - f x‖ + ‖f (x + ε) - ε • g x - f x‖ := norm_sub_le _ _
      _ ≤ (‖f (x + ε)‖ + ‖f x‖) + ‖h‖ * ε * ε := add_le_add (norm_sub_le _ _) hm
      _ ≤ 2 * ‖f‖ + ‖h‖ * ε * ε := by
        linarith [f.norm_apply_le (x + ε), f.norm_apply_le x]
  apply le_of_mul_le_mul_left (a := ε) _ hε
  calc
    ε * ‖g x‖ ≤ 2 * ‖f‖ + ‖h‖ * ε * ε := hbound
    _ = ε * ((2 / ε) * ‖f‖ + ε * ‖h‖) := by field_simp

end BUC
