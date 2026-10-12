/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianFourierConvolution
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

@[expose] public section

/-!
# Gaussian convolution through a finite diffusion eigenbasis

This is the matrix version of the Gaussian multiplier identity. A finite family
of Gaussian kernels is followed by fixed bounded operators and a fixed coordinate
map. All finite-coordinate and bounded-linear-map interchanges are justified in
the Banach norm.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

variable {V E G H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [Fintype ι]

/-- A finite diagonal Gaussian kernel, with arbitrary bounded coordinate maps. -/
def diagonalGaussianKernel (b : ι → ℝ) (A : ι → E →L[ℂ] G)
    (J : (ι → G) →L[ℂ] H) (x : V) : E →L[ℂ] H :=
  J.comp (ContinuousLinearMap.pi fun i ↦ gaussianDensity (4 * b i)⁻¹ x • A i)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace E] [CompleteSpace G] [CompleteSpace H] [Fintype ι] in
@[simp]
theorem diagonalGaussianKernel_apply (b : ι → ℝ) (A : ι → E →L[ℂ] G)
    (J : (ι → G) →L[ℂ] H) (x : V) (v : E) :
    diagonalGaussianKernel b A J x v = J (fun i ↦ gaussianDensity (4 * b i)⁻¹ x • A i v) := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace E] [CompleteSpace G] [CompleteSpace H] in
/-- Norm-continuity of the finite diagonal operator kernel. -/
theorem continuous_diagonalGaussianKernel (b : ι → ℝ) (A : ι → E →L[ℂ] G)
    (J : (ι → G) →L[ℂ] H) : Continuous (diagonalGaussianKernel (V := V) b A J) := by
  let L : (ι → E →L[ℂ] G) →L[ℂ] E →L[ℂ] H :=
    (ContinuousLinearMap.compL ℂ E (ι → G) H J).comp
      (ContinuousLinearMap.piEquivL ℂ E (fun _ : ι ↦ G)).toContinuousLinearMap
  exact L.continuous.comp (continuous_pi fun i ↦ (continuous_gaussianDensity _).smul continuous_const)

omit [CompleteSpace E] [CompleteSpace G] [CompleteSpace H] in
/-- The diagonal kernel is integrable in operator norm. -/
theorem integrable_diagonalGaussianKernel (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (A : ι → E →L[ℂ] G) (J : (ι → G) →L[ℂ] H) :
    Integrable (diagonalGaussianKernel (V := V) b A J) := by
  let L : (ι → E →L[ℂ] G) →L[ℂ] E →L[ℂ] H :=
    (ContinuousLinearMap.compL ℂ E (ι → G) H J).comp
      (ContinuousLinearMap.piEquivL ℂ E (fun _ : ι ↦ G)).toContinuousLinearMap
  exact L.integrable_comp (Integrable.of_eval fun i ↦
    (integrable_gaussianDensity (by have := hb i; positivity : 0 < (4 * b i)⁻¹)).smul_const (A i))

/-- Fixed bounded maps commute with an absolutely convergent inverse Fourier integral. -/
theorem map_oscillatoryIntegral (A : E →L[ℂ] G) {g : V → E}
    (hg : Continuous g) (hi : Integrable g) (x : V) :
    A (oscillatoryIntegral g x) = oscillatoryIntegral (fun ξ ↦ A (g ξ)) x := by
  rw [oscillatoryIntegral, ← A.integral_comp_comm (integrable_oscillatory_of_integrable hg hi x)]
  simp only [map_smul, oscillatoryIntegral]

/-- The inverse transform of the diagonal Gaussian multiplier is the corresponding
operator-kernel convolution. This keeps the order of all coefficient maps. -/
theorem diagonalGaussian_fourier_convolution (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (A : ι → E →L[ℂ] G) (J : (ι → G) →L[ℂ] H) {g : V → E}
    (hg : Continuous g) (hi : Integrable g) (x : V) :
    oscillatoryIntegral (fun ξ : V ↦ J (fun i ↦
      Complex.exp (-(b i : ℂ) * ‖ξ‖ ^ 2) • A i (g ξ))) x =
      ∫ y : V, diagonalGaussianKernel b A J y (oscillatoryIntegral g (x - y)) := by
  let u (ξ : V) : ι → G := fun i ↦ Complex.exp (-(b i : ℂ) * ‖ξ‖ ^ 2) • A i (g ξ)
  have hc : Continuous u := continuous_pi fun i ↦ by dsimp [u]; fun_prop
  have hui : Integrable u := Integrable.of_eval fun i ↦
    integrable_gaussian_mul_of_integrable (hb i).le ((A i).continuous.comp hg) ((A i).integrable_comp hi)
  rw [← map_oscillatoryIntegral J hc hui x]
  have hcoord (i : ι) : (oscillatoryIntegral u x) i =
      ∫ y : V, gaussianDensity (4 * b i)⁻¹ y • A i (oscillatoryIntegral g (x - y)) := by
    rw [oscillatoryIntegral, eval_integral (fun i ↦
      (integrable_oscillatory_of_integrable hc hui x).eval i)]
    change oscillatoryIntegral (fun ξ : V ↦
      Complex.exp (-(b i : ℂ) * ‖ξ‖ ^ 2) • A i (g ξ)) x = _
    simpa only [Function.comp_def, map_oscillatoryIntegral (A i) hg hi] using!
      oscillatoryIntegral_gaussian_mul_eq_convolution (hb i)
        ((A i).continuous.comp hg) ((A i).integrable_comp hi) x
  have hy : Integrable (fun y : V ↦ fun i ↦
      gaussianDensity (4 * b i)⁻¹ y • A i (oscillatoryIntegral g (x - y))) := by
    apply Integrable.of_eval
    intro i
    simp_rw [map_oscillatoryIntegral (A i) hg hi]
    exact integrable_gaussian_oscillatory_convolution (hb i)
      ((A i).continuous.comp hg) ((A i).integrable_comp hi) x
  simp only [diagonalGaussianKernel_apply]
  rw [J.integral_comp_comm hy]
  congr 1
  funext i
  rw [eval_integral (fun i ↦ hy.eval i), hcoord]

omit [CompleteSpace E] in
/-- The diagonal kernel itself is the normalized inverse transform of its
Gaussian operator symbol. -/
theorem diagonalGaussianKernel_eq_fourierIntegral (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (A : ι → E →L[ℂ] G) (J : (ι → G) →L[ℂ] H) (x : V) (v : E) :
    diagonalGaussianKernel b A J x v = ((2 * Real.pi) ^ Module.finrank ℝ V)⁻¹ •
      oscillatoryIntegral (fun ξ : V ↦ J (fun i ↦
        Complex.exp (-(b i : ℂ) * ‖ξ‖ ^ 2) • A i v)) x := by
  let u (ξ : V) : ι → G := fun i ↦ Complex.exp (-(b i : ℂ) * ‖ξ‖ ^ 2) • A i v
  have hc : Continuous u := continuous_pi fun i ↦ by dsimp [u]; fun_prop
  have hi : Integrable u := Integrable.of_eval fun i ↦ by
    simpa only [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] using
      integrable_oscillatory_gaussian_smul (hb i) (0 : V) (A i v)
  rw [← map_oscillatoryIntegral J hc hi x]
  have hJ (a : ℝ) (w : ι → G) : a • J w = J (a • w) :=
    ((J.restrictScalars ℝ).map_smul a w).symm
  rw [hJ, diagonalGaussianKernel_apply]
  congr 1
  funext i
  rw [Pi.smul_apply, oscillatoryIntegral,
    eval_integral (fun i ↦ (integrable_oscillatory_of_integrable hc hi x).eval i)]
  exact (normalized_oscillatoryIntegral_gaussian_smul (hb i) x (A i v)).symm

omit [CompleteSpace E] [CompleteSpace G] [CompleteSpace H]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Pointwise domination of the operator kernel by the finite sum of scalar densities. -/
theorem norm_diagonalGaussianKernel_le (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (A : ι → E →L[ℂ] G) (J : (ι → G) →L[ℂ] H) (x : V) :
    ‖diagonalGaussianKernel b A J x‖ ≤
      ‖J‖ * ∑ i, gaussianDensity (4 * b i)⁻¹ x * ‖A i‖ := by
  classical
  have hρ (i : ι) : 0 ≤ gaussianDensity (4 * b i)⁻¹ x :=
    gaussianDensity_nonneg (by have := hb i; positivity) x
  have hnorm (i : ι) : ‖gaussianDensity (4 * b i)⁻¹ x • A i‖ =
      gaussianDensity (4 * b i)⁻¹ x * ‖A i‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ i)]
  have hpi : ‖ContinuousLinearMap.pi (fun i ↦ gaussianDensity (4 * b i)⁻¹ x • A i)‖ ≤
      ∑ i, gaussianDensity (4 * b i)⁻¹ x * ‖A i‖ := by
    apply ContinuousLinearMap.norm_pi_le_of_le
    · intro i
      rw [hnorm]
      exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (hρ j) (norm_nonneg _)) (Finset.mem_univ i)
    · exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hρ i) (norm_nonneg _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left hpi (norm_nonneg J))

omit [CompleteSpace E] [CompleteSpace G] [CompleteSpace H] in
/-- The Gaussian kernel mass bound is independent of the positive diffusion scales. -/
theorem integral_norm_diagonalGaussianKernel_le (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (A : ι → E →L[ℂ] G) (J : (ι → G) →L[ℂ] H) :
    (∫ x : V, ‖diagonalGaussianKernel b A J x‖) ≤ ‖J‖ * ∑ i, ‖A i‖ := by
  have hp (i : ι) : 0 < (4 * b i)⁻¹ := by have := hb i; positivity
  have hi (i : ι) : Integrable (fun x : V ↦ gaussianDensity (4 * b i)⁻¹ x * ‖A i‖) :=
    (integrable_gaussianDensity (hp i)).mul_const _
  calc
    _ ≤ ∫ x : V, ‖J‖ * ∑ i, gaussianDensity (4 * b i)⁻¹ x * ‖A i‖ :=
      integral_mono (integrable_diagonalGaussianKernel b hb A J).norm
        ((integrable_finsetSum _ (fun i _ ↦ hi i)).const_mul _) (norm_diagonalGaussianKernel_le b hb A J)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hi i)]
      simp_rw [integral_mul_const, integral_gaussianDensity (hp _), one_mul]

end

end Planarwave
