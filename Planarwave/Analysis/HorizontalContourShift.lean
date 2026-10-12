/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Shifting a Gaussian-dominated horizontal contour

This is the one-dimensional Cauchy step in Section 3's Fourier contour shift.
Integrate over finite rectangles, estimate the vertical sides by the Gaussian
tail, and pass to the absolutely convergent horizontal integrals. The result
is Banach-valued and applies in particular to bounded-operator-valued symbols.
-/

open Filter MeasureTheory Set Topology

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Absolute convergence of a horizontal contour under a Gaussian bound. -/
theorem integrable_horizontal_of_gaussian_bound {f : ℂ → F} {β γ b C : ℝ}
    (hb : 0 < b)
    (hf : ∀ z : ℂ, β ≤ z.im → z.im ≤ γ → DifferentiableAt ℂ f z)
    (hbound : ∀ z : ℂ, β ≤ z.im → z.im ≤ γ → ‖f z‖ ≤ C * Real.exp (-b * z.re ^ 2))
    {r : ℝ} (hr : r ∈ Icc β γ) :
    Integrable (fun x : ℝ ↦ f (x + r * Complex.I)) := by
  have hc : Continuous (fun x : ℝ ↦ f (x + r * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hf (x + r * Complex.I) (by simpa using hr.1) (by simpa using hr.2)).continuousAt.comp
      (f := fun x : ℝ ↦ (x : ℂ) + r * Complex.I) (by fun_prop)
  apply ((integrable_exp_neg_mul_sq hb).const_mul C).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  simpa using hbound (x + r * Complex.I) (by simpa using hr.1) (by simpa using hr.2)

omit [CompleteSpace F] in
/-- Cauchy's theorem shifts the horizontal contour through a Gaussian-dominated strip. -/
theorem integral_horizontal_eq_of_gaussian_bound {f : ℂ → F} {β γ b C : ℝ}
    (hβγ : β ≤ γ) (hb : 0 < b)
    (hf : ∀ z : ℂ, β ≤ z.im → z.im ≤ γ → DifferentiableAt ℂ f z)
    (hbound : ∀ z : ℂ, β ≤ z.im → z.im ≤ γ → ‖f z‖ ≤ C * Real.exp (-b * z.re ^ 2)) :
    (∫ x : ℝ, f (x + β * Complex.I)) = ∫ x : ℝ, f (x + γ * Complex.I) := by
  let V (T : ℝ) := ∫ y : ℝ in β..γ, f (T + y * Complex.I)
  let H (r T : ℝ) := ∫ x : ℝ in -T..T, f (x + r * Complex.I)
  have hVbound (T : ℝ) : ‖V T‖ ≤ (C * Real.exp (-b * T ^ 2)) * |γ - β| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hy' : y ∈ Ioc β γ := by simpa only [uIoc_of_le hβγ] using hy
    simpa using hbound (T + y * Complex.I) (by simpa using hy'.1.le) (by simpa using hy'.2)
  have hmajorant : Tendsto (fun T : ℝ ↦ (C * Real.exp (-b * T ^ 2)) * |γ - β|) atTop (𝓝 0) := by
    have hpow : Tendsto (fun T : ℝ ↦ T ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have hneg : Tendsto (fun T : ℝ ↦ -b * T ^ 2) atTop atBot :=
      hpow.const_mul_atTop_of_neg (neg_neg_of_pos hb)
    simpa using ((Real.tendsto_exp_atBot.comp hneg).const_mul C).mul_const |γ - β|
  have hVpos : Tendsto V atTop (𝓝 0) := squeeze_zero_norm hVbound hmajorant
  have hVneg : Tendsto (fun T ↦ V (-T)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hmajorant
    intro T
    simpa only [neg_sq] using hVbound (-T)
  have hH (r : ℝ) (hr : r ∈ Icc β γ) :
      Tendsto (H r) atTop (𝓝 (∫ x : ℝ, f (x + r * Complex.I))) :=
    intervalIntegral_tendsto_integral (integrable_horizontal_of_gaussian_bound hb hf hbound hr)
      tendsto_neg_atTop_atBot tendsto_id
  have hrectangle (T : ℝ) :
      H β T - H γ T + Complex.I • V T - Complex.I • V (-T) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-T, β⟩ ⟨T, γ⟩
    intro z hz
    have him : z.im ∈ Icc β γ := by
      simpa only [Set.mem_preimage, uIcc_of_le hβγ] using hz.2
    exact (hf z him.1 him.2).differentiableWithinAt
  have hlim := ((hH β ⟨le_rfl, hβγ⟩).sub (hH γ ⟨hβγ, le_rfl⟩)).add
    (hVpos.const_smul Complex.I) |>.sub (hVneg.const_smul Complex.I)
  have heq := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun T ↦ (hrectangle T).symm))
  exact sub_eq_zero.mp (by simpa using heq)

end

end Planarwave
