/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.L1DerivativeInterpolation

@[expose] public section

/-!
# An L1 estimate for the longitudinal adjoint ODE

Invertible diffusion controls the second derivative. L1 interpolation absorbs
the drift, giving a bound independent of the regularization scale. The source
is an independent integrable function, so the estimate applies to mollified
variable-coefficient equations without commuting multiplication and smoothing.
-/

open MeasureTheory

namespace Planarwave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first two derivatives are bounded in L1 by the solution and source. -/
theorem exists_l1_adjointODE_derivative_bound (D : F →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ a, ‖a‖ ≤ K * ‖D a‖) (c : ℝ) :
    ∃ C > 0, ∀ u v w q : ℝ → F,
      Continuous v → Continuous w →
      (∀ x, HasDerivAt u (v x) x) → (∀ x, HasDerivAt v (w x) x) →
      Integrable u → Integrable v → Integrable w → Integrable q →
      (∀ x, D (w x) - c • v x + q x = 0) →
      (∫ x, ‖v x‖) + (∫ x, ‖w x‖) ≤ C * ((∫ x, ‖u x‖) + ∫ x, ‖q x‖) := by
  let d := K * ‖c‖
  have hd : 0 ≤ d := by positivity
  let ε := 1 / (2 * (d + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : 2 * (d + 1) * ε = 1 := by dsimp [ε]; field_simp
  have hdε : d * ε ≤ 1 / 2 := by nlinarith
  let C₀ := 2 / ε
  let C₂ := 2 * K + 2 * d * C₀
  let C₁ := C₀ + ε * C₂
  have hC₀ : 0 ≤ C₀ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨1 + C₁ + C₂, by positivity, ?_⟩
  intro u v w q hv hw huv hvw hui hvi hwi hqi heq
  let U := ∫ x, ‖u x‖
  let V := ∫ x, ‖v x‖
  let W := ∫ x, ‖w x‖
  let Q := ∫ x, ‖q x‖
  have hU : 0 ≤ U := integral_nonneg fun _ ↦ norm_nonneg _
  have hW : 0 ≤ W := integral_nonneg fun _ ↦ norm_nonneg _
  have hQ : 0 ≤ Q := integral_nonneg fun _ ↦ norm_nonneg _
  have hraw : W ≤ d * V + K * Q := by
    have hsource : Integrable (fun x ↦ ‖c‖ * ‖v x‖ + ‖q x‖) :=
      (hvi.norm.const_mul ‖c‖).add hqi.norm
    calc
      W ≤ ∫ x, K * (‖c‖ * ‖v x‖ + ‖q x‖) := by
        apply integral_mono hwi.norm (hsource.const_mul K)
        intro x
        have hDx : D (w x) = c • v x - q x := by
          have := heq x
          simpa [sub_eq_add_neg, add_comm] using
            sub_eq_iff_eq_add.mp (eq_sub_of_add_eq this)
        calc
          _ ≤ K * ‖D (w x)‖ := hD _
          _ ≤ K * (‖c‖ * ‖v x‖ + ‖q x‖) := by
            rw [hDx]
            exact mul_le_mul_of_nonneg_left (by simpa only [norm_smul] using norm_sub_le (c • v x) (q x)) hK
      _ = d * V + K * Q := by
        rw [integral_const_mul, integral_add (hvi.norm.const_mul ‖c‖) hqi.norm, integral_const_mul]
        dsimp [d, V, Q]
        ring
  have hinterp : V ≤ C₀ * U + ε * W :=
    integral_norm_firstDerivative_le u v w hv hw huv hvw hui hvi hwi hε
  have hsecond : W ≤ 2 * K * Q + 2 * d * C₀ * U := by
    have := mul_le_mul_of_nonneg_left hinterp hd
    have := mul_le_mul_of_nonneg_right hdε hW
    nlinarith
  have hsecond' : W ≤ C₂ * (U + Q) := by
    calc
      _ ≤ 2 * K * Q + 2 * d * C₀ * U := hsecond
      _ ≤ 2 * K * (U + Q) + 2 * d * C₀ * (U + Q) := by gcongr <;> linarith
      _ = _ := by dsimp [C₂]; ring
  have hfirst : V ≤ C₁ * (U + Q) := by
    calc
      _ ≤ C₀ * U + ε * W := hinterp
      _ ≤ C₀ * (U + Q) + ε * (C₂ * (U + Q)) := by gcongr; linarith
      _ = _ := by dsimp [C₁]; ring
  change V + W ≤ (1 + C₁ + C₂) * (U + Q)
  nlinarith

end Planarwave
