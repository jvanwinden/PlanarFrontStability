/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ResolventVerticalBounds
public import Planarwave.Analysis.VerticalContourShift

@[expose] public section

/-!
# Squared-resolvent contours in a spectral gap

The differentiated Laplace inversion kernel is holomorphic off the spectrum.
Sectorial bounds justify absolute convergence and movement of its vertical
contour. On a line with real part `β`, the integral is bounded by a constant
times `exp (β t)`. Identifying this integral with `t S(t)` is a separate step.
-/

open Filter MeasureTheory Set Topology

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

/-- The kernel for differentiated Laplace inversion; the sign convention for
`A - z I` disappears after taking the square. -/
def squaredResolventKernel (A : ClosedOperator ℂ E Dom) (t : ℝ) (z : ℂ) : E →L[ℂ] E :=
  Complex.exp ((t : ℂ) * z) • (A.ambientResolvent z).comp (A.ambientResolvent z)

theorem differentiableAt_squaredResolventKernel (A : ClosedOperator ℂ E Dom)
    (t : ℝ) {z : ℂ} (hz : A.IsInResolvent z) :
    DifferentiableAt ℂ (A.squaredResolventKernel t) z := by
  have hR := (A.hasDerivAt_ambientResolvent hz).differentiableAt
  have he : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.exp ((t : ℂ) * w)) z := by fun_prop
  exact he.smul (hR.clm_comp hR)

/-- Uniform inverse-quadratic domination of the kernel on a vertical strip. -/
theorem norm_squaredResolventKernel_le (A : ClosedOperator ℂ E Dom)
    {C β γ : ℝ}
    (hbound : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → ‖A.ambientResolvent z‖ ≤ C / (1 + |z.im|))
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hβ : β ≤ z.re) (hγ : z.re ≤ γ) :
    ‖A.squaredResolventKernel t z‖ ≤ (Real.exp (t * γ) * C ^ 2) * (1 + z.im ^ 2)⁻¹ := by
  have hline : ∀ y : ℝ, ‖A.ambientResolvent (z.re + y * Complex.I)‖ ≤ C / (1 + |y|) := by
    intro y
    simpa using hbound (z.re + y * Complex.I) (by simpa using hβ) (by simpa using hγ)
  have hsquare : ‖(A.ambientResolvent z).comp (A.ambientResolvent z)‖ ≤
      C ^ 2 * (1 + z.im ^ 2)⁻¹ := by
    simpa only [Complex.re_add_im] using A.norm_ambientResolvent_sq_le hline z.im
  have hexp : Real.exp (((t : ℂ) * z).re) ≤ Real.exp (t * γ) := by
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_left hγ ht
  rw [squaredResolventKernel, norm_smul, Complex.norm_exp]
  exact (mul_le_mul hexp hsquare (norm_nonneg _) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm

/-- The squared-resolvent contour may be shifted across any spectrum-free
strip, including from a growth half-plane to a line inside a spectral gap. -/
theorem integral_squaredResolventKernel_eq (A : ClosedOperator ℂ E Dom)
    {a C₀ Ω β γ : ℝ} (ha : 0 < a) (hβγ : β ≤ γ)
    (hsector : ∀ z : ℂ, Ω < z.re + a * |z.im| →
      ‖A.ambientResolvent z‖ ≤ C₀ / (z.re + a * |z.im| - Ω))
    (hres : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → A.IsInResolvent z)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ y : ℝ, A.squaredResolventKernel t (β + y * Complex.I)) =
      ∫ y : ℝ, A.squaredResolventKernel t (γ + y * Complex.I) := by
  obtain ⟨C, _, hC⟩ := A.exists_ambientResolvent_vertical_bound ha hsector hres
  exact integral_vertical_eq_of_quadratic_bound hβγ
    (fun z hβ hγ ↦ A.differentiableAt_squaredResolventKernel t (hres z hβ hγ))
    (fun _ hβ hγ ↦ A.norm_squaredResolventKernel_le hC ht hβ hγ)

/-- Absolute convergence and an exponential bound on a squared-resolvent
contour at a fixed real part. The constant is independent of time. -/
theorem exists_integral_squaredResolventKernel_bound (A : ClosedOperator ℂ E Dom)
    {a C₀ Ω β : ℝ} (ha : 0 < a)
    (hsector : ∀ z : ℂ, Ω < z.re + a * |z.im| →
      ‖A.ambientResolvent z‖ ≤ C₀ / (z.re + a * |z.im| - Ω))
    (hres : ∀ z : ℂ, z.re = β → A.IsInResolvent z) :
    ∃ C > 0, ∀ t : ℝ, 0 ≤ t →
      Integrable (fun y : ℝ ↦ A.squaredResolventKernel t (β + y * Complex.I)) ∧
      ‖∫ y : ℝ, A.squaredResolventKernel t (β + y * Complex.I)‖ ≤ C * Real.exp (β * t) := by
  have hstrip : ∀ z : ℂ, β ≤ z.re → z.re ≤ β → A.IsInResolvent z :=
    fun z h₁ h₂ ↦ hres z (le_antisymm h₂ h₁)
  obtain ⟨C, hC, hbound⟩ := A.exists_ambientResolvent_vertical_bound ha hsector hstrip
  refine ⟨C ^ 2 * Real.pi, by positivity, ?_⟩
  intro t ht
  have hdiff := fun z h₁ h₂ ↦ A.differentiableAt_squaredResolventKernel t (hstrip z h₁ h₂)
  have hkernel := fun z h₁ h₂ ↦ A.norm_squaredResolventKernel_le hbound ht (z := z) h₁ h₂
  refine ⟨integrable_vertical_of_quadratic_bound hdiff hkernel ⟨le_rfl, le_rfl⟩, ?_⟩
  calc
    ‖∫ y : ℝ, A.squaredResolventKernel t (β + y * Complex.I)‖ ≤
        ∫ y : ℝ, (Real.exp (t * β) * C ^ 2) * (1 + y ^ 2)⁻¹ := by
      apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
      filter_upwards [] with y
      simpa using hkernel (β + y * Complex.I) (by simp) (by simp)
    _ = (C ^ 2 * Real.pi) * Real.exp (β * t) := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
      rw [mul_comm t β]
      ring

end

end Planarwave.ClosedOperator
