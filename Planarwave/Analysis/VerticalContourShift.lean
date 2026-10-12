/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Shifting absolutely convergent vertical contour integrals

Cauchy's theorem on finite rectangles, followed by the vanishing of the
horizontal sides, shifts a Banach-valued integral across a closed vertical
strip. The inverse-quadratic majorant is tailored to squared resolvents in
the spectral-to-growth argument.
-/

open Filter MeasureTheory Set Topology

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- An inverse-quadratic vertical bound implies absolute convergence on every
line of the strip. -/
theorem integrable_vertical_of_quadratic_bound {f : ℂ → F} {β γ C : ℝ}
    (hf : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → DifferentiableAt ℂ f z)
    (hbound : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → ‖f z‖ ≤ C * (1 + z.im ^ 2)⁻¹)
    {r : ℝ} (hr : r ∈ Icc β γ) :
    Integrable (fun y : ℝ ↦ f (r + y * Complex.I)) := by
  have hc : Continuous (fun y : ℝ ↦ f (r + y * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hdiff := hf (r + y * Complex.I) (by simpa using hr.1) (by simpa using hr.2)
    exact hdiff.continuousAt.comp (f := fun y : ℝ ↦ (r : ℂ) + y * Complex.I) (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  simpa using hbound (r + y * Complex.I) (by simpa using hr.1) (by simpa using hr.2)

omit [CompleteSpace F] in
/-- Cauchy contour shifting on an unbounded strip. The horizontal edges
vanish in norm and the two vertical edges converge absolutely. -/
theorem integral_vertical_eq_of_quadratic_bound {f : ℂ → F} {β γ C : ℝ}
    (hβγ : β ≤ γ)
    (hf : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → DifferentiableAt ℂ f z)
    (hbound : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → ‖f z‖ ≤ C * (1 + z.im ^ 2)⁻¹) :
    (∫ y : ℝ, f (β + y * Complex.I)) = ∫ y : ℝ, f (γ + y * Complex.I) := by
  let H (T : ℝ) := ∫ x : ℝ in β..γ, f (x + T * Complex.I)
  let V (r T : ℝ) := ∫ y : ℝ in -T..T, f (r + y * Complex.I)
  have hHbound (T : ℝ) : ‖H T‖ ≤ (C * (1 + T ^ 2)⁻¹) * |γ - β| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Ioc β γ := by simpa only [uIoc_of_le hβγ] using hx
    simpa using hbound (x + T * Complex.I) (by simpa using hx'.1.le) (by simpa using hx'.2)
  have hmajorant : Tendsto (fun T : ℝ ↦ (C * (1 + T ^ 2)⁻¹) * |γ - β|) atTop (𝓝 0) := by
    have hp : Tendsto (fun T : ℝ ↦ 1 + T ^ 2) atTop atTop :=
      tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
    simpa using ((tendsto_inv_atTop_zero.comp hp).const_mul C).mul_const |γ - β|
  have hHpos : Tendsto H atTop (𝓝 0) := squeeze_zero_norm (fun T ↦ hHbound T) hmajorant
  have hHneg : Tendsto (fun T ↦ H (-T)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hmajorant
    intro T
    simpa only [neg_sq] using hHbound (-T)
  have hV (r : ℝ) (hr : r ∈ Icc β γ) :
      Tendsto (V r) atTop (𝓝 (∫ y : ℝ, f (r + y * Complex.I))) :=
    intervalIntegral_tendsto_integral (integrable_vertical_of_quadratic_bound hf hbound hr)
      tendsto_neg_atTop_atBot tendsto_id
  have hrectangle (T : ℝ) :
      H (-T) - H T + Complex.I • V γ T - Complex.I • V β T = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨β, -T⟩ ⟨γ, T⟩
    intro z hz
    have hre : z.re ∈ Icc β γ := by
      simpa only [Set.mem_preimage, uIcc_of_le hβγ] using hz.1
    exact (hf z hre.1 hre.2).differentiableWithinAt
  have hlim := ((hHneg.sub hHpos).add ((hV γ ⟨hβγ, le_rfl⟩).const_smul Complex.I)).sub
    ((hV β ⟨le_rfl, hβγ⟩).const_smul Complex.I)
  have hzero : Complex.I • (∫ y : ℝ, f (γ + y * Complex.I)) -
      Complex.I • (∫ y : ℝ, f (β + y * Complex.I)) = 0 := by
    have heq := tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun T ↦ (hrectangle T).symm))
    simpa using heq
  exact (smul_right_injective F Complex.I_ne_zero) (sub_eq_zero.mp hzero).symm

end

end Planarwave
