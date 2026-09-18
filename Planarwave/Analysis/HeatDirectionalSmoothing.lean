/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianOrthogonalSplit
public import Mathlib.Analysis.Calculus.Rademacher

@[expose] public section

/-!
# Directional Gaussian smoothing

Use the independent scalar coordinate in an orthogonal Gaussian splitting to apply the
real-line smoothing theorem in any unit direction.
-/

open Filter Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Restrict a BUC function to a line through a point in the orthogonal Gaussian slice. -/
def gaussianOrthogonalSlice (s : ℝ) (v : E) (f : BUC E F) (x z : E) : BUC ℝ F :=
  f.comp (fun r : ℝ => x + s • (z - ⟪v, z⟫ • v) + r • v)
    (uniformContinuous_const.add (ContinuousLinearMap.toSpanSingleton ℝ v).uniformContinuous)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
@[simp]
theorem gaussianOrthogonalSlice_apply (s : ℝ) (v : E) (f : BUC E F) (x z : E) (r : ℝ) :
    gaussianOrthogonalSlice s v f x z r = f (x + s • (z - ⟪v, z⟫ • v) + r • v) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Restricting to the slice cannot increase the BUC norm. -/
theorem norm_gaussianOrthogonalSlice_le (s : ℝ) (v : E) (f : BUC E F) (x z : E) :
    ‖gaussianOrthogonalSlice s v f x z‖ ≤ ‖f‖ := BUC.norm_comp_le _ _ _

/-- Multidimensional heat flow along a unit direction is an average of one-dimensional
Gaussian smoothings of the orthogonal slices. -/
theorem heatFlow_add_smul_eq_integral_gaussianSmooth (a t : ℝ) (v : E) (hv : ‖v‖ = 1)
    (f : BUC E F) (x : E) (r : ℝ) :
    heatFlow a t f (x + r • v) =
      ∫ z : E, gaussianSmooth (heatScale a t)
        (gaussianOrthogonalSlice (heatScale a t) v f x z) r ∂stdGaussian E := by
  rw [heatFlow, integral_stdGaussian_orthogonalSplit v hv
    (fun z : E => f (x + r • v + heatScale a t • z))
    (f.continuous.comp (by fun_prop))
    (integrable_comp_add_heatScale f.continuous ‖f‖ f.norm_apply_le _)]
  apply integral_congr_ae
  filter_upwards with z
  rw [gaussianSmooth]
  apply integral_congr_ae
  filter_upwards with q
  rw [gaussianOrthogonalSlice_apply]
  congr 1
  simp only [orthogonalGaussianSplit, smul_add, add_smul, smul_smul]
  abel

/-- Differentiating heat flow along an arbitrary unit direction. -/
theorem hasDerivAt_heatFlow_unit_direction {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (v : E) (hv : ‖v‖ = 1) (f : BUC E F) (x : E) (r : ℝ) :
    HasDerivAt (fun q => heatFlow a t f (x + q • v))
      (∫ z : E, gaussianSmoothD1 (heatScale a t)
        (gaussianOrthogonalSlice (heatScale a t) v f x z) r ∂stdGaussian E) r := by
  let s := heatScale a t
  have hs : 0 < s := heatScale_pos_of_pos ha ht
  let A : ℝ → E → F := fun q z => gaussianSmooth s (gaussianOrthogonalSlice s v f x z) q
  let A' : ℝ → E → F := fun q z => gaussianSmoothD1 s (gaussianOrthogonalSlice s v f x z) q
  have hm (q : ℝ) : AEStronglyMeasurable (A q) (stdGaussian E) := by
    have hc : Continuous (fun p : E × ℝ =>
        f (x + s • (p.1 - ⟪v, p.1⟫ • v) + (q + s * p.2) • v)) :=
      f.continuous.comp (by fun_prop)
    exact hc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hm' (q : ℝ) : AEStronglyMeasurable (A' q) (stdGaussian E) := by
    have hc : Continuous (fun p : E × ℝ => (p.2 / s) •
        f (x + s • (p.1 - ⟪v, p.1⟫ • v) + (q + s * p.2) • v)) :=
      Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))
    exact hc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hbound (q : ℝ) (z : E) : ‖A' q z‖ ≤ ‖f‖ / s :=
    (norm_gaussianSmoothD1_le s hs _ q).trans
      (div_le_div_of_nonneg_right (norm_gaussianOrthogonalSlice_le s v f x z) hs.le)
  have hi : Integrable (A r) (stdGaussian E) := by
    apply (integrable_const ‖f‖).mono' (hm r)
    filter_upwards with z
    exact (norm_integral_le_of_norm_le_const
      (ae_of_all (stdGaussian ℝ) fun q => (gaussianOrthogonalSlice s v f x z).norm_apply_le
        (r + s * q))).trans (by simpa using norm_gaussianOrthogonalSlice_le s v f x z)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := A) (F' := A') (bound := fun _ : E => ‖f‖ / s) (s := Set.univ)
    Filter.univ_mem (Filter.Eventually.of_forall hm) hi (hm' r)
    (ae_of_all _ fun z q _ => hbound q z) (integrable_const _)
    (ae_of_all _ fun z q _ => hasDerivAt_gaussianSmooth s hs _ q)).2
  have heq : (fun q => heatFlow a t f (x + q • v)) = fun q => ∫ z, A q z ∂stdGaussian E :=
    funext fun q => heatFlow_add_smul_eq_integral_gaussianSmooth a t v hv f x q
  rw [heq]
  exact hd

/-- The directional derivative is the basis-free first Hermite kernel. -/
theorem gaussianGradientKernel_unit_eq_integral (a t : ℝ) (v : E) (hv : ‖v‖ = 1)
    (f : BUC E F) (x : E) (r : ℝ) :
    gaussianGradientKernel (heatScale a t) f (x + r • v) v =
      ∫ z : E, gaussianSmoothD1 (heatScale a t)
        (gaussianOrthogonalSlice (heatScale a t) v f x z) r ∂stdGaussian E := by
  let s := heatScale a t
  have hi : Integrable (fun w : E => (⟪w, v⟫ / s) • f (x + r • v + s • w))
      (stdGaussian E) := by
    have h := (integrable_gaussianGradientKernel s f (x + r • v)).apply_continuousLinearMap v
    refine h.congr (ae_of_all _ fun w => ?_)
    simp [innerSL_apply_apply, div_eq_mul_inv, mul_comm]
  rw [gaussianGradientKernel_apply, integral_stdGaussian_orthogonalSplit v hv
    (fun w : E => (⟪w, v⟫ / s) • f (x + r • v + s • w))
    (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))) hi]
  apply integral_congr_ae
  filter_upwards with z
  rw [gaussianSmoothD1]
  apply integral_congr_ae
  filter_upwards with q
  have hinner : ⟪orthogonalGaussianSplit v (z, q), v⟫ = q := by
    simp [orthogonalGaussianSplit, inner_add_left, inner_sub_left, real_inner_smul_left,
      hv, real_inner_comm z v]
  rw [hinner, gaussianOrthogonalSlice_apply]
  congr 2
  simp only [orthogonalGaussianSplit, smul_add, add_smul, smul_smul]
  abel

/-- Pointwise directional heat differentiation in terms of the gradient kernel. -/
theorem hasDerivAt_heatFlow_unit_direction_kernel {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (v : E) (hv : ‖v‖ = 1) (f : BUC E F) (x : E) (r : ℝ) :
    HasDerivAt (fun q => heatFlow a t f (x + q • v))
      (gaussianGradientKernel (heatScale a t) f (x + r • v) v) r := by
  rw [gaussianGradientKernel_unit_eq_integral a t v hv f x r]
  exact hasDerivAt_heatFlow_unit_direction ha ht v hv f x r

/-- A dimension-independent bound on the derivative along any unit direction. -/
theorem norm_gaussianGradientKernel_unit_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (v : E) (hv : ‖v‖ = 1) (f : BUC E F) (x : E) :
    ‖gaussianGradientKernel (heatScale a t) f x v‖ ≤ ‖f‖ / heatScale a t := by
  have hs := heatScale_pos_of_pos ha ht
  have h := gaussianGradientKernel_unit_eq_integral a t v hv f x 0
  simp only [zero_smul, add_zero] at h
  rw [h]
  simpa using norm_integral_le_of_norm_le_const (ae_of_all (stdGaussian E) fun z =>
    (norm_gaussianSmoothD1_le _ hs (gaussianOrthogonalSlice _ v f x z) 0).trans
      (div_le_div_of_nonneg_right (norm_gaussianOrthogonalSlice_le _ v f x z) hs.le))

/-- A dimension-independent global Lipschitz estimate for positive-time heat averaging. -/
theorem lipschitzWith_heatFlow {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    LipschitzWith ⟨‖f‖ / heatScale a t, div_nonneg (norm_nonneg _) (heatScale_pos_of_pos ha ht).le⟩
      (heatFlow a t f) := by
  let C : NNReal := ⟨‖f‖ / heatScale a t, div_nonneg (norm_nonneg _) (heatScale_pos_of_pos ha ht).le⟩
  have hline (v : E) (hv : ‖v‖ = 1) (x : E) :
      LipschitzWith C (fun r : ℝ => heatFlow a t f (x + r • v)) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      (fun r => (hasDerivAt_heatFlow_unit_direction_kernel ha ht v hv f x r).differentiableAt)
    intro r
    rw [(hasDerivAt_heatFlow_unit_direction_kernel ha ht v hv f x r).deriv]
    exact norm_gaussianGradientKernel_unit_le ha ht v hv f _
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  by_cases hxy : x = y
  · simp [hxy]
  have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  let v := ‖x - y‖⁻¹ • (x - y)
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, Real.norm_eq_abs, hn]
  have heq : y + ‖x - y‖ • v = x := by simp [v, smul_smul, hn]
  have h := (hline v hv y).dist_le_mul ‖x - y‖ 0
  simpa only [heq, zero_smul, add_zero, dist_zero_right, norm_norm, dist_eq_norm] using h

/-- The first Hermite kernel is the Fréchet derivative of multidimensional heat flow. -/
theorem hasFDerivAt_heatFlow {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) (x : E) :
    HasFDerivAt (heatFlow a t f) (gaussianGradientKernel (heatScale a t) f x) x := by
  apply (lipschitzWith_heatFlow ha ht f).hasFDerivAt_of_hasLineDerivAt_of_closure
    (s := Metric.sphere 0 1) subset_closure
  intro v hv
  have hv' : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
  simpa only [HasLineDerivAt, zero_smul, add_zero] using
    hasDerivAt_heatFlow_unit_direction_kernel ha ht v hv' f x 0

end

end Planarwave
