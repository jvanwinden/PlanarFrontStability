/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianFourierKernel
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Frequency-time Fubini under a uniform Gaussian bound

In a Fourier-space Duhamel integrand, the Gaussian weights at times `t-r` and
`r` combine to a Gaussian at time `t`. The resulting majorant justifies Fubini
over frequency and the finite time interval, without a singular endpoint bound.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedSpace ℂ F] in
/-- Uniform Gaussian domination on a finite time interval gives joint Bochner
integrability, not only separate integrability. -/
theorem integrable_time_frequency_of_gaussian_bound {g : ℝ × V → F}
    (hg : Continuous g) {b C t : ℝ} (hb : 0 < b)
    (hbound : ∀ r ∈ Icc 0 t, ∀ ξ, ‖g (r, ξ)‖ ≤ C * Real.exp (-b * ‖ξ‖ ^ 2)) :
    Integrable g ((volume.restrict (Ioc 0 t)).prod volume) := by
  have hi : Integrable (fun p : ℝ × V ↦ C * Real.exp (-b * ‖p.2‖ ^ 2))
      ((volume.restrict (Ioc 0 t)).prod volume) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ))
        (volume.restrict (Ioc 0 t))).mul_prod ((integrable_gaussian_norm hb).const_mul C)
  apply hi.mono' hg.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hg.norm.measurable (by fun_prop))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact Filter.Eventually.of_forall fun ξ ↦ hbound r ⟨hr.1.le, hr.2⟩ ξ

/-- Adding the real-contour Fourier phase does not change the Gaussian bound. -/
theorem integrable_time_oscillatory_of_gaussian_bound {g : ℝ × V → F}
    (hg : Continuous g) {b C t : ℝ} (hb : 0 < b)
    (hbound : ∀ r ∈ Icc 0 t, ∀ ξ, ‖g (r, ξ)‖ ≤ C * Real.exp (-b * ‖ξ‖ ^ 2)) (x : V) :
    Integrable (fun p : ℝ × V ↦ Complex.exp (Complex.I * (⟪p.2, x⟫ : ℂ)) • g p)
      ((volume.restrict (Ioc 0 t)).prod volume) := by
  apply integrable_time_frequency_of_gaussian_bound (by fun_prop) hb
  intro r hr ξ
  rw [norm_oscillatoryIntegrand (fun ξ ↦ g (r, ξ)) x ξ]
  exact hbound r hr ξ

/-- Frequency inversion commutes with Duhamel integration under the joint bound. -/
theorem oscillatoryIntegral_intervalIntegral_swap {g : ℝ × V → F}
    (hg : Continuous g) {b C t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    (hbound : ∀ r ∈ Icc 0 t, ∀ ξ, ‖g (r, ξ)‖ ≤ C * Real.exp (-b * ‖ξ‖ ^ 2)) (x : V) :
    oscillatoryIntegral (fun ξ ↦ ∫ r in 0..t, g (r, ξ)) x =
      ∫ r in 0..t, oscillatoryIntegral (fun ξ ↦ g (r, ξ)) x := by
  unfold oscillatoryIntegral
  simp_rw [← intervalIntegral.integral_smul]
  exact (intervalIntegral_integral_swap (by
    simpa only [uIoc_of_le ht, Function.uncurry] using!
      integrable_time_oscillatory_of_gaussian_bound hg hb hbound x)).symm

/-- The inverted forcing is integrable in time in the Banach norm. -/
theorem intervalIntegrable_oscillatoryIntegral_of_gaussian_bound {g : ℝ × V → F}
    (hg : Continuous g) {b C t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    (hbound : ∀ r ∈ Icc 0 t, ∀ ξ, ‖g (r, ξ)‖ ≤ C * Real.exp (-b * ‖ξ‖ ^ 2)) (x : V) :
    IntervalIntegrable (fun r ↦ oscillatoryIntegral (fun ξ ↦ g (r, ξ)) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  exact (integrable_time_oscillatory_of_gaussian_bound hg hb hbound x).integral_prod_left

end

end Planarwave
