/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Coordinates
import Planarwave.Analysis.HeatFlow

/-!
# Independent transverse and longitudinal Gaussian coordinates

The coordinate splitting used by the challenge sends the product of the
transverse and longitudinal standard Gaussians to the full spatial Gaussian.
The proof uses the Euclidean inner product, not the max norm of the product
space on which `coordinateEquiv` takes values.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d : ℕ}

/-- The challenge's assembled coordinates form an orthogonal splitting. -/
theorem inner_full_full (hd : 2 ≤ d) (y y' : ℝ^(d - 1)) (z z' : ℝ) :
    ⟪(full y z : ℝ^d), full y' z'⟫ = ⟪y, y'⟫ + z * z' := by
  cases d with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel] at y y'
    simp [PiLp.inner_apply, RCLike.inner_apply, full, Fin.sum_univ_castSucc,
      mul_comm]

/-- Inner products with a full spatial point separate into the two coordinate factors. -/
theorem inner_full_coordinates (hd : 2 ≤ d) (y : ℝ^(d - 1)) (z : ℝ) (x : ℝ^d) :
    ⟪full y z, x⟫ = ⟪y, transverse x⟫ + z * horizontal x := by
  conv_lhs => rw [← full_transverse_horizontal hd x]
  exact inner_full_full hd y (transverse x) z (horizontal x)

/-- Pythagoras for the transverse and longitudinal coordinates. -/
theorem norm_sq_coordinates (hd : 2 ≤ d) (x : ℝ^d) :
    ‖transverse x‖ ^ 2 + (horizontal x) ^ 2 = ‖x‖ ^ 2 := by
  have h := inner_full_coordinates hd (transverse x) (horizontal x) x
  rw [full_transverse_horizontal hd, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, ← sq] at h
  exact h.symm

/-- Independent Gaussian coordinates assemble to the full spatial standard Gaussian. -/
theorem stdGaussian_map_full (hd : 2 ≤ d) :
    ((stdGaussian (ℝ^(d - 1))).prod (stdGaussian ℝ)).map
      (fun p : ℝ^(d - 1) × ℝ ↦ (full p.1 p.2 : ℝ^d)) = stdGaussian (ℝ^d) := by
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_apply, integral_map continuous_full.measurable.aemeasurable (by fun_prop)]
  simp_rw [inner_full_coordinates hd, Complex.ofReal_add, Complex.ofReal_mul,
    add_mul, Complex.exp_add]
  rw [integral_prod_mul
    (fun y : ℝ^(d - 1) ↦ Complex.exp ((⟪y, transverse x⟫ : ℂ) * Complex.I))
    (fun z : ℝ ↦ Complex.exp ((z : ℂ) * (horizontal x : ℂ) * Complex.I))]
  have hz : (∫ z : ℝ, Complex.exp ((z : ℂ) * (horizontal x : ℂ) * Complex.I)
      ∂stdGaussian ℝ) = Complex.exp (-((horizontal x : ℂ) ^ 2) / 2) := by
    simpa [charFun_apply, RCLike.inner_apply, Real.norm_eq_abs,
      ← Complex.ofReal_pow, sq_abs, mul_comm] using charFun_stdGaussian (horizontal x)
  rw [hz, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hc : (‖transverse x‖ : ℂ) ^ 2 + (horizontal x : ℂ) ^ 2 = (‖x‖ : ℂ) ^ 2 := by
    exact_mod_cast norm_sq_coordinates hd x
  linear_combination -(1 / 2 : ℂ) * hc

/-- The corresponding Fubini formula for integrable continuous Banach-valued data. -/
theorem integral_stdGaussian_full {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hd : 2 ≤ d) (g : ℝ^d → F) (hg : Continuous g)
    (hint : Integrable g (stdGaussian (ℝ^d))) :
    ∫ x, g x ∂stdGaussian (ℝ^d) =
      ∫ y : ℝ^(d - 1), ∫ z : ℝ, g (full y z) ∂stdGaussian ℝ ∂stdGaussian (ℝ^(d - 1)) := by
  let A : ℝ^(d - 1) × ℝ → ℝ^d := fun p ↦ full p.1 p.2
  have hm : Measurable A := continuous_full.measurable
  have hi : Integrable (g ∘ A) ((stdGaussian (ℝ^(d - 1))).prod (stdGaussian ℝ)) := by
    apply (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).mp
    rwa [stdGaussian_map_full hd]
  conv_lhs => rw [← stdGaussian_map_full hd]
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]
  exact integral_prod _ hi

/-- Gaussian displacements respect the linear coordinate splitting. -/
theorem full_add_smul_full (hd : 2 ≤ d) (y y' : ℝ^(d - 1)) (z z' s : ℝ) :
    (full y z : ℝ^d) + s • full y' z' = full (y + s • y') (z + s * z') := by
  change (coordinateEquiv hd).symm (y, z) + s • (coordinateEquiv hd).symm (y', z') =
    (coordinateEquiv hd).symm ((y, z) + s • (y', z'))
  rw [map_add, map_smul]

/-- Full-dimensional heat averaging is successive transverse and longitudinal
heat averaging, with no integrability requirement on the bounded initial datum. -/
theorem heatFlow_full_coordinates {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (hd : 2 ≤ d) (a t : ℝ)
    (f : ℝ^d → F) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (y : ℝ^(d - 1)) (z : ℝ) :
    heatFlow a t f (full y z) =
      heatFlow a t (fun y' : ℝ^(d - 1) ↦ heatFlow a t (fun z' : ℝ ↦ f (full y' z')) z) y := by
  have h := integral_stdGaussian_full hd
    (fun x : ℝ^d ↦ f (full y z + heatScale a t • x)) (by fun_prop)
    (integrable_comp_add_heatScale hf C hC (full y z))
  simpa only [heatFlow, full_add_smul_full hd, smul_eq_mul] using h

end

end Planarwave
