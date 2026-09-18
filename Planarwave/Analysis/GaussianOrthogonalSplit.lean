/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSmoothingMultidimensional

@[expose] public section

/-!
# Orthogonal splitting of a standard Gaussian

Replace the component along a unit vector by an independent standard real Gaussian. The
result still has the standard Gaussian law. This allows one-dimensional smoothing estimates
to be used along arbitrary directions without choosing coordinates on the orthogonal complement.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal component of the first Gaussian, with an independent real coordinate along `v`. -/
def orthogonalGaussianSplit (v : E) (p : E × ℝ) : E :=
  p.1 - ⟪v, p.1⟫ • v + p.2 • v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_orthogonalGaussianSplit (v : E) : Continuous (orthogonalGaussianSplit v) := by
  unfold orthogonalGaussianSplit
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Scalar products separate into independent Gaussian factors. -/
theorem inner_orthogonalGaussianSplit (v w : E) (p : E × ℝ) :
    ⟪orthogonalGaussianSplit v p, w⟫ =
      ⟪p.1, w - ⟪v, w⟫ • v⟫ + p.2 * ⟪v, w⟫ := by
  simp only [orthogonalGaussianSplit, inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_sub_right, inner_smul_right]
  rw [real_inner_comm p.1 v]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pythagoras for a unit-vector projection. -/
theorem norm_sq_orthogonal_component_add (v w : E) (hv : ‖v‖ = 1) :
    ‖w - ⟪v, w⟫ • v‖ ^ 2 + ⟪v, w⟫ ^ 2 = ‖w‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs,
    inner_smul_right, real_inner_comm w v]
  ring

/-- The split Gaussian has the same law as the original isotropic standard Gaussian. -/
theorem stdGaussian_map_orthogonalGaussianSplit (v : E) (hv : ‖v‖ = 1) :
    ((stdGaussian E).prod (stdGaussian ℝ)).map (orthogonalGaussianSplit v) = stdGaussian E := by
  have hm := (continuous_orthogonalGaussianSplit v).measurable
  apply Measure.ext_of_charFun
  funext w
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [inner_orthogonalGaussianSplit, Complex.ofReal_add, Complex.ofReal_mul,
    add_mul, Complex.exp_add]
  rw [integral_prod_mul
    (fun z : E => Complex.exp ((⟪z, w - ⟪v, w⟫ • v⟫ : ℂ) * Complex.I))
    (fun r : ℝ => Complex.exp ((r : ℂ) * (⟪v, w⟫ : ℂ) * Complex.I))]
  have hr : (∫ z : ℝ, Complex.exp ((z : ℂ) * (⟪v, w⟫ : ℂ) * Complex.I)
      ∂stdGaussian ℝ) = Complex.exp (-((⟪v, w⟫ : ℂ) ^ 2) / 2) := by
    have h := charFun_stdGaussian (E := ℝ) ⟪v, w⟫
    simpa [charFun_apply, RCLike.inner_apply, Real.norm_eq_abs,
      ← Complex.ofReal_pow, sq_abs, mul_comm] using h
  rw [hr, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hnorm := norm_sq_orthogonal_component_add v w hv
  have hc : ((‖w - ⟪v, w⟫ • v‖ : ℂ) ^ 2) + (⟪v, w⟫ : ℂ) ^ 2 = (‖w‖ : ℂ) ^ 2 := by
    exact_mod_cast hnorm
  linear_combination -(1 / 2 : ℂ) * hc

/-- The integral form of the orthogonal Gaussian splitting, for integrable continuous data. -/
theorem integral_stdGaussian_orthogonalSplit {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (v : E) (hv : ‖v‖ = 1) (g : E → F)
    (hg : Continuous g) (hint : Integrable g (stdGaussian E)) :
    ∫ w, g w ∂stdGaussian E =
      ∫ z : E, ∫ r : ℝ, g (orthogonalGaussianSplit v (z, r))
        ∂stdGaussian ℝ ∂stdGaussian E := by
  have hm := (continuous_orthogonalGaussianSplit v).measurable
  have hi : Integrable (g ∘ orthogonalGaussianSplit v)
      ((stdGaussian E).prod (stdGaussian ℝ)) := by
    apply (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).mp
    rwa [stdGaussian_map_orthogonalGaussianSplit v hv]
  conv_lhs => rw [← stdGaussian_map_orthogonalGaussianSplit v hv]
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]
  simpa only [Function.comp_def] using integral_prod _ hi

end

end Planarwave
