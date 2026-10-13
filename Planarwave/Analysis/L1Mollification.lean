/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.L1Smoothing
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Smooth approximations of integrable longitudinal data

Normalized compactly supported kernels produce smooth BUC approximations,
with integrable first and second derivatives. Their L1 norms are bounded by
the original L1 norm, and they converge to the original data almost everywhere.
The derivative bounds here are not uniform in the smoothing scale.
-/

open MeasureTheory Filter
open scoped ContDiff Convolution Topology

namespace Planarwave

noncomputable section

/-- A fixed shrinking sequence of bumps, with outer-to-inner radius ratio two. -/
def longitudinalBump (j : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / ((j : ℝ) + 1)
  rOut := 2 / ((j : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

theorem longitudinalBump_rOut_tendsto :
    Tendsto (fun j ↦ (longitudinalBump j).rOut) atTop (𝓝 0) := by
  simpa only [longitudinalBump, mul_one_div, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

/-- The normalized scalar kernel, bundled as a BUC function. -/
def longitudinalMollifier (j : ℕ) : BUC ℝ ℝ :=
  BUC.ofCompactSupport ((longitudinalBump j).normed volume)
    (longitudinalBump j).continuous_normed (longitudinalBump j).hasCompactSupport_normed

theorem contDiff_longitudinalMollifier (j : ℕ) :
    ContDiff ℝ ∞ (longitudinalMollifier j : ℝ → ℝ) :=
  (longitudinalBump j).contDiff_normed

theorem hasCompactSupport_longitudinalMollifier (j : ℕ) :
    HasCompactSupport (longitudinalMollifier j : ℝ → ℝ) :=
  (longitudinalBump j).hasCompactSupport_normed

theorem integrable_longitudinalMollifier (j : ℕ) :
    Integrable (longitudinalMollifier j : ℝ → ℝ) :=
  (longitudinalBump j).integrable_normed

theorem integral_norm_longitudinalMollifier (j : ℕ) :
    (∫ x, ‖longitudinalMollifier j x‖) = 1 := by
  change (∫ x, ‖(longitudinalBump j).normed volume x‖) = 1
  simp_rw [Real.norm_eq_abs, abs_of_nonneg ((longitudinalBump j).nonneg_normed _)]
  exact (longitudinalBump j).integral_normed

/-- The first derivative of the compactly supported kernel. -/
def longitudinalMollifierFirst (j : ℕ) : BUC ℝ ℝ :=
  BUC.ofCompactSupport (deriv (longitudinalMollifier j))
    (contDiff_infty_iff_deriv.mp (contDiff_longitudinalMollifier j)).2.continuous
    (hasCompactSupport_longitudinalMollifier j).deriv

theorem contDiff_longitudinalMollifierFirst (j : ℕ) :
    ContDiff ℝ ∞ (longitudinalMollifierFirst j : ℝ → ℝ) :=
  (contDiff_infty_iff_deriv.mp (contDiff_longitudinalMollifier j)).2

/-- The second derivative of the compactly supported kernel. -/
def longitudinalMollifierSecond (j : ℕ) : BUC ℝ ℝ :=
  BUC.ofCompactSupport (deriv (longitudinalMollifierFirst j))
    (contDiff_infty_iff_deriv.mp (contDiff_longitudinalMollifierFirst j)).2.continuous
    (hasCompactSupport_longitudinalMollifier j).deriv.deriv

theorem hasDerivAt_longitudinalMollifier (j : ℕ) (x : ℝ) :
    HasDerivAt (longitudinalMollifier j) (longitudinalMollifierFirst j x) x :=
  ((contDiff_longitudinalMollifier j).differentiable (by simp) x).hasDerivAt

theorem hasDerivAt_longitudinalMollifierFirst (j : ℕ) (x : ℝ) :
    HasDerivAt (longitudinalMollifierFirst j) (longitudinalMollifierSecond j x) x :=
  ((contDiff_longitudinalMollifierFirst j).differentiable (by simp) x).hasDerivAt

theorem integrable_longitudinalMollifierFirst (j : ℕ) :
    Integrable (longitudinalMollifierFirst j : ℝ → ℝ) :=
  (longitudinalMollifierFirst j).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_longitudinalMollifier j).deriv

theorem integrable_longitudinalMollifierSecond (j : ℕ) :
    Integrable (longitudinalMollifierSecond j : ℝ → ℝ) :=
  (longitudinalMollifierSecond j).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_longitudinalMollifier j).deriv.deriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth BUC approximations of integrable longitudinal data. -/
def longitudinalMollification (u : ℝ → F) (hu : Integrable u) (j : ℕ) : BUC ℝ F :=
  l1SmoothingBUC (longitudinalMollifier j) u hu

theorem contDiff_longitudinalMollification {u : ℝ → F} (hu : Integrable u) (j : ℕ) :
    ContDiff ℝ ∞ (longitudinalMollification u hu j : ℝ → F) :=
  contDiff_l1Smoothing _ (contDiff_longitudinalMollifier j)
    (hasCompactSupport_longitudinalMollifier j) hu

theorem deriv_longitudinalMollification {u : ℝ → F} (hu : Integrable u) (j : ℕ) :
    deriv (longitudinalMollification u hu j) = l1Smoothing (longitudinalMollifierFirst j) u :=
  funext fun x ↦ (hasDerivAt_l1Smoothing _ _ (hasDerivAt_longitudinalMollifier j) hu x).deriv

theorem deriv_deriv_longitudinalMollification {u : ℝ → F} (hu : Integrable u) (j : ℕ) :
    deriv (deriv (longitudinalMollification u hu j)) =
      l1Smoothing (longitudinalMollifierSecond j) u := by
  rw [deriv_longitudinalMollification]
  exact funext fun x ↦
    (hasDerivAt_l1Smoothing _ _ (hasDerivAt_longitudinalMollifierFirst j) hu x).deriv

theorem integrable_longitudinalMollification {u : ℝ → F} (hu : Integrable u) (j : ℕ) :
    Integrable (longitudinalMollification u hu j : ℝ → F) :=
  integrable_l1Smoothing _ (integrable_longitudinalMollifier j) hu

theorem integrable_deriv_longitudinalMollification {u : ℝ → F} (hu : Integrable u) (j : ℕ) :
    Integrable (deriv (longitudinalMollification u hu j)) := by
  rw [deriv_longitudinalMollification]
  exact integrable_l1Smoothing _ (integrable_longitudinalMollifierFirst j) hu

theorem integrable_deriv_deriv_longitudinalMollification {u : ℝ → F}
    (hu : Integrable u) (j : ℕ) :
    Integrable (deriv (deriv (longitudinalMollification u hu j))) := by
  rw [deriv_deriv_longitudinalMollification]
  exact integrable_l1Smoothing _ (integrable_longitudinalMollifierSecond j) hu

/-- The mass bound does not deteriorate as the smoothing scale tends to zero. -/
theorem integral_norm_longitudinalMollification_le {u : ℝ → F} (hu : Integrable u) (j : ℕ) :
    (∫ x, ‖longitudinalMollification u hu j x‖) ≤ ∫ x, ‖u x‖ := by
  simpa only [integral_norm_longitudinalMollifier, one_mul] using!
    integral_norm_l1Smoothing_le (longitudinalMollifier j) (integrable_longitudinalMollifier j) hu

/-- Mollification depends only on the almost-everywhere class of the data. -/
theorem longitudinalMollification_congr_ae {u v : ℝ → F}
    (hu : Integrable u) (hv : Integrable v) (heq : u =ᵐ[volume] v) (j : ℕ) :
    longitudinalMollification u hu j = longitudinalMollification v hv j := by
  apply BUC.ext
  intro x
  apply integral_congr_ae
  filter_upwards [heq] with z hz
  rw [hz]

/-- Normalized nonnegative mollifiers preserve an essential supremum bound. -/
theorem norm_longitudinalMollification_le_of_ae_bound {u : ℝ → F} (hu : Integrable u)
    {M : ℝ} (hb : ∀ᵐ z, ‖u z‖ ≤ M) (j : ℕ) (x : ℝ) :
    ‖longitudinalMollification u hu j x‖ ≤ M := by
  have hi := ((integrable_longitudinalMollifier j).norm.comp_sub_left x).mul_const M
  calc
    _ ≤ ∫ z, ‖longitudinalMollifier j (x - z)‖ * M := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [hb] with z hz
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = M := by
      rw [integral_mul_const, integral_sub_left_eq_self (fun z ↦ ‖longitudinalMollifier j z‖),
        integral_norm_longitudinalMollifier, one_mul]

/-- For continuous integrable data convergence holds at every point. -/
theorem tendsto_longitudinalMollification_of_continuous [CompleteSpace F]
    {u : ℝ → F} (hu : Integrable u) (hc : Continuous u) (x : ℝ) :
    Tendsto (fun j ↦ longitudinalMollification u hu j x) atTop (𝓝 (u x)) := by
  simpa only [MeasureTheory.convolution_eq_swap, ContinuousLinearMap.lsmul_apply] using!
    ContDiffBump.convolution_tendsto_right_of_continuous
      longitudinalBump_rOut_tendsto (μ := volume) hc x

/-- Lebesgue differentiation identifies the almost-everywhere limit with the
original measurable data, not just with an unspecified distribution. -/
theorem ae_tendsto_longitudinalMollification [CompleteSpace F] {u : ℝ → F} (hu : Integrable u) :
    ∀ᵐ x, Tendsto (fun j ↦ longitudinalMollification u hu j x) atTop (𝓝 (u x)) := by
  have hratio : ∀ᶠ j : ℕ in atTop, (longitudinalBump j).rOut ≤ 2 * (longitudinalBump j).rIn :=
    Eventually.of_forall fun j ↦ by dsimp [longitudinalBump]; simp only [mul_one_div, le_refl]
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    longitudinalBump_rOut_tendsto hratio hu.locallyIntegrable
  simpa only [MeasureTheory.convolution_eq_swap, ContinuousLinearMap.lsmul_apply] using! h

end

end Planarwave
