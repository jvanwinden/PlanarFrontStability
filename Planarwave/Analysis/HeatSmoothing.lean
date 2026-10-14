/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatSemigroup
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

/-!
# One-dimensional heat smoothing on BUC

This file proves the one-dimensional instance of the smoothing estimate used in Lemma 3.2 of
the paper.  The proof follows the Gaussian-kernel argument: translation of a Gaussian is written
with its exponential density ratio, differentiation is passed under the integral, and the first
two differentiated kernels are estimated by their Gaussian moments.

The statements are vector-valued: the initial datum takes values in an arbitrary real Banach
space.  In one space dimension the gradient and Laplacian are respectively `deriv` and the
second iterated derivative.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace Planarwave

noncomputable section

section GaussianPreliminaries

/-- Mathlib's abstract standard Gaussian on `ℝ` is the usual real Gaussian of variance one. -/
theorem stdGaussian_real : stdGaussian ℝ = gaussianReal 0 1 := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_gaussianReal]
  congr 1
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, zero_sub]
  norm_cast
  simp only [Real.norm_eq_abs, one_mul]
  rw [sq_abs]
  ring

/-- Every polynomial times `exp (c |x|)` is integrable for the standard real Gaussian. -/
theorem integrable_abs_pow_mul_exp_abs_stdGaussian (c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n * Real.exp (|c| * |x|)) (stdGaussian ℝ) := by
  rw [stdGaussian_real]
  have hp : Integrable (fun x : ℝ => |x| ^ n * Real.exp (|c| * x))
      (gaussianReal 0 1) := by
    simpa using
      (integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
        (X := id) (μ := gaussianReal 0 1) (v := |c|) (by simp) n)
  have hn : Integrable (fun x : ℝ => |x| ^ n * Real.exp (-|c| * x))
      (gaussianReal 0 1) := by
    simpa using
      (integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
        (X := id) (μ := gaussianReal 0 1) (v := -|c|) (by simp) n)
  refine (hp.add hn).mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg x) _) (Real.exp_pos _).le)]
  by_cases hx : 0 ≤ x
  · simp only [Pi.add_apply, abs_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  · simp only [Pi.add_apply, abs_of_neg (lt_of_not_ge hx)]
    have : |c| * -x = -|c| * x := by ring
    rw [this]
    have hxle : x ≤ 0 := (lt_of_not_ge hx).le
    exact le_add_of_nonneg_left
      (mul_nonneg (pow_nonneg (neg_nonneg.mpr hxle) _) (Real.exp_pos _).le)

theorem integrable_abs_stdGaussian :
    Integrable (fun x : ℝ => |x|) (stdGaussian ℝ) := by
  simpa using integrable_abs_pow_mul_exp_abs_stdGaussian 0 1

theorem integrable_sq_stdGaussian :
    Integrable (fun x : ℝ => x ^ 2) (stdGaussian ℝ) := by
  rw [stdGaussian_real]
  simpa using
    (integrable_pow_of_mem_interior_integrableExpSet
      (X := id) (μ := gaussianReal 0 1) (by simp) 2)

/-- The second moment of the standard real Gaussian is one. -/
theorem integral_sq_stdGaussian : ∫ x : ℝ, x ^ 2 ∂(stdGaussian ℝ) = 1 := by
  rw [stdGaussian_real]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := (1 : NNReal))
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- A deliberately simple first absolute-moment estimate, sufficient for Lemma 3.2. -/
theorem integral_abs_stdGaussian_le_one :
    ∫ x : ℝ, |x| ∂(stdGaussian ℝ) ≤ 1 := by
  have hpoint : ∀ x : ℝ, |x| ≤ (x ^ 2 + 1) / 2 := by
    intro x
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  calc
    ∫ x : ℝ, |x| ∂(stdGaussian ℝ) ≤ ∫ x : ℝ, (x ^ 2 + 1) / 2 ∂(stdGaussian ℝ) := by
      exact integral_mono integrable_abs_stdGaussian
        ((integrable_sq_stdGaussian.add (integrable_const 1)).div_const 2) hpoint
    _ = 1 := by
      rw [integral_div, integral_add, integral_sq_stdGaussian]
      · simp
      · exact integrable_sq_stdGaussian
      · exact integrable_const 1

/-- The second differentiated Gaussian kernel has `L¹` norm at most two. -/
theorem integral_abs_sq_sub_one_stdGaussian_le_two :
    ∫ x : ℝ, |x ^ 2 - 1| ∂(stdGaussian ℝ) ≤ 2 := by
  have hint : Integrable (fun x : ℝ => |x ^ 2 - 1|) (stdGaussian ℝ) := by
    refine (integrable_sq_stdGaussian.sub (integrable_const 1)).norm.congr ?_
    filter_upwards with x
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  calc
    ∫ x : ℝ, |x ^ 2 - 1| ∂(stdGaussian ℝ) ≤
        ∫ x : ℝ, (x ^ 2 + 1) ∂(stdGaussian ℝ) := by
      exact integral_mono hint (integrable_sq_stdGaussian.add (integrable_const 1))
        (fun x => by rw [abs_le]; constructor <;> nlinarith [sq_nonneg x])
    _ = 2 := by
      rw [integral_add integrable_sq_stdGaussian (integrable_const 1), integral_sq_stdGaussian]
      norm_num

end GaussianPreliminaries

section KernelRepresentations

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Gaussian smoothing with spatial scale `s`.  For `s = sqrt (2at)` this is `heatFlow a t`. -/
def gaussianSmooth (s : ℝ) (f : ℝ → F) (x : ℝ) : F :=
  ∫ z, f (x + s * z) ∂(stdGaussian ℝ)

/-- The first differentiated Gaussian-kernel representation. -/
def gaussianSmoothD1 (s : ℝ) (f : ℝ → F) (x : ℝ) : F :=
  ∫ z, (z / s) • f (x + s * z) ∂(stdGaussian ℝ)

/-- The second differentiated Gaussian-kernel representation. -/
def gaussianSmoothD2 (s : ℝ) (f : ℝ → F) (x : ℝ) : F :=
  ∫ z, ((z ^ 2 - 1) / s ^ 2) • f (x + s * z) ∂(stdGaussian ℝ)

theorem heatFlow_real_eq_gaussianSmooth (a t : ℝ) (f : ℝ → F) :
    heatFlow a t f = gaussianSmooth (heatScale a t) f := by
  funext x
  simp only [heatFlow, gaussianSmooth, smul_eq_mul]

private theorem gaussianPDFReal_shift_ratio (u z : ℝ) :
    gaussianPDFReal u 1 z = Real.exp (u * z - u ^ 2 / 2) * gaussianPDFReal 0 1 z := by
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]
  have hexp : Real.exp (-(z - u) ^ 2 / 2) =
      Real.exp (u * z - u ^ 2 / 2) * Real.exp (-(z - 0) ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Cameron--Martin's density-ratio identity in the elementary one-dimensional form needed here. -/
private theorem gaussianSmooth_add_eq_integral_exp
    (s : ℝ) (hs : s ≠ 0) (f : ℝ → F) (hf : Continuous f) (x h : ℝ) :
    gaussianSmooth s f (x + h) =
      ∫ z, Real.exp ((h / s) * z - (h / s) ^ 2 / 2) • f (x + s * z)
        ∂(stdGaussian ℝ) := by
  rw [gaussianSmooth, stdGaussian_real]
  let g : ℝ → F := fun z => f (x + s * z)
  have hg : Continuous g := hf.comp (by fun_prop)
  calc
    (∫ z, f (x + h + s * z) ∂gaussianReal 0 1) =
        ∫ z, g ((h / s) + z) ∂gaussianReal 0 1 := by
      congr 1
      funext z
      dsimp [g]
      congr 1
      field_simp [hs]
      ring
    _ = ∫ z, g z ∂((gaussianReal 0 1).map ((h / s) + ·)) := by
      rw [integral_map]
      · fun_prop
      · exact hg.aestronglyMeasurable
    _ = ∫ z, g z ∂gaussianReal (h / s) 1 := by
      rw [gaussianReal_map_const_add]
      simp
    _ = ∫ z, gaussianPDFReal (h / s) 1 z • g z := by
      rw [integral_gaussianReal_eq_integral_smul]
      norm_num
    _ = ∫ z, gaussianPDFReal 0 1 z •
        (Real.exp ((h / s) * z - (h / s) ^ 2 / 2) • g z) := by
      congr 1
      funext z
      rw [gaussianPDFReal_shift_ratio]
      simp [mul_smul, mul_comm]
    _ = ∫ z, Real.exp ((h / s) * z - (h / s) ^ 2 / 2) • g z
        ∂gaussianReal 0 1 := by
      rw [integral_gaussianReal_eq_integral_smul]
      norm_num

private theorem gaussianSmoothD1_add_eq_integral_exp
    (s : ℝ) (hs : s ≠ 0) (f : ℝ → F) (hf : Continuous f) (x h : ℝ) :
    gaussianSmoothD1 s f (x + h) =
      ∫ z, (((z - h / s) / s) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) •
        f (x + s * z) ∂(stdGaussian ℝ) := by
  rw [gaussianSmoothD1, stdGaussian_real]
  let g : ℝ → F := fun z => ((z - h / s) / s) • f (x + s * z)
  have hg : Continuous g := by
    apply Continuous.smul
    · fun_prop
    · exact hf.comp (by fun_prop)
  calc
    (∫ z, (z / s) • f (x + h + s * z) ∂gaussianReal 0 1) =
        ∫ z, g ((h / s) + z) ∂gaussianReal 0 1 := by
      congr 1
      funext z
      dsimp [g]
      congr 1
      · field_simp [hs]
        ring
      · congr 1
        field_simp [hs]
        ring
    _ = ∫ z, g z ∂((gaussianReal 0 1).map ((h / s) + ·)) := by
      rw [integral_map]
      · fun_prop
      · exact hg.aestronglyMeasurable
    _ = ∫ z, g z ∂gaussianReal (h / s) 1 := by
      rw [gaussianReal_map_const_add]
      simp
    _ = ∫ z, gaussianPDFReal (h / s) 1 z • g z := by
      rw [integral_gaussianReal_eq_integral_smul]
      norm_num
    _ = ∫ z, gaussianPDFReal 0 1 z •
        ((((z - h / s) / s) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) •
          f (x + s * z)) := by
      congr 1
      funext z
      change gaussianPDFReal (h / s) 1 z • (((z - h / s) / s) • f (x + s * z)) =
        gaussianPDFReal 0 1 z •
          ((((z - h / s) / s) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) •
            f (x + s * z))
      rw [gaussianPDFReal_shift_ratio]
      simp only [smul_smul]
      apply congrArg (fun r : ℝ => r • f (x + s * z))
      ring
    _ = ∫ z, (((z - h / s) / s) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) •
        f (x + s * z) ∂gaussianReal 0 1 := by
      rw [integral_gaussianReal_eq_integral_smul]
      norm_num

private theorem hasDerivAt_gaussianShiftWeight (s : ℝ) (hs : s ≠ 0) (z h : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp ((r / s) * z - (r / s) ^ 2 / 2))
      ((z / s - h / s ^ 2) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) h := by
  have hlin : HasDerivAt (fun r : ℝ => r / s) (1 / s) h :=
    (hasDerivAt_id h).div_const s
  have harg₀ := (hlin.mul_const z).sub ((hlin.pow 2).div_const 2)
  change HasDerivAt (fun r : ℝ => (r / s) * z - (r / s) ^ 2 / 2) _ h at harg₀
  have harg : HasDerivAt (fun r : ℝ => (r / s) * z - (r / s) ^ 2 / 2)
      (z / s - h / s ^ 2) h := by
    convert harg₀ using 1
    norm_num
    field_simp [hs]
  have he := (Real.hasDerivAt_exp _).comp h harg
  change HasDerivAt (fun r : ℝ => Real.exp ((r / s) * z - (r / s) ^ 2 / 2)) _ h at he
  convert he using 1
  ring

private def gaussianSmoothD1Dominating (s C z : ℝ) : ℝ :=
  (|z| / s + 1 / s ^ 2) * Real.exp ((1 / s) * |z|) * C

private theorem integrable_gaussianSmoothD1Dominating
    (s C : ℝ) (hs : 0 < s) :
    Integrable (gaussianSmoothD1Dominating s C) (stdGaussian ℝ) := by
  have h₀ : Integrable (fun z : ℝ => Real.exp ((1 / s) * |z|)) (stdGaussian ℝ) := by
    simpa [abs_div, abs_of_pos hs] using
      integrable_abs_pow_mul_exp_abs_stdGaussian (1 / s) 0
  have h₁ : Integrable (fun z : ℝ => |z| * Real.exp ((1 / s) * |z|))
      (stdGaussian ℝ) := by
    simpa [abs_div, abs_of_pos hs] using
      integrable_abs_pow_mul_exp_abs_stdGaussian (1 / s) 1
  have hout := ((h₁.const_mul (1 / s)).add (h₀.const_mul (1 / s ^ 2))).mul_const C
  convert hout using 1
  funext z
  simp only [gaussianSmoothD1Dominating, Pi.add_apply]
  ring

private theorem norm_gaussianShiftWeight_deriv_le
    (s C z h : ℝ) (hs : 0 < s) (hh : h ∈ Metric.ball 0 1) (hC : 0 ≤ C) :
    ‖((z / s - h / s ^ 2) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2))‖ * C ≤
      gaussianSmoothD1Dominating s C z := by
  have hah : |h| < 1 := by simpa [Real.dist_eq] using hh
  have hcoeff : |z / s - h / s ^ 2| ≤ |z| / s + 1 / s ^ 2 := by
    calc
      |z / s - h / s ^ 2| ≤ |z / s| + |h / s ^ 2| := by
        simpa using abs_sub_le (z / s) 0 (h / s ^ 2)
      _ = |z| / s + |h| / s ^ 2 := by rw [abs_div, abs_div, abs_of_pos hs, abs_of_pos (sq_pos_of_pos hs)]
      _ ≤ |z| / s + 1 / s ^ 2 := by
        gcongr
  have hexpArg : (h / s) * z - (h / s) ^ 2 / 2 ≤ (1 / s) * |z| := by
    calc
      (h / s) * z - (h / s) ^ 2 / 2 ≤ (h / s) * z := by
        nlinarith [sq_nonneg (h / s)]
      _ ≤ |(h / s) * z| := le_abs_self _
      _ = (|h| / s) * |z| := by rw [abs_mul, abs_div, abs_of_pos hs]
      _ ≤ (1 / s) * |z| := by
        gcongr
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  unfold gaussianSmoothD1Dominating
  gcongr

/-- Gaussian convolution differentiates once even when the BUC datum itself is not
differentiable.  The derivative is obtained by differentiating the Gaussian kernel. -/
theorem hasDerivAt_gaussianSmooth (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) (x : ℝ) :
    HasDerivAt (gaussianSmooth s f) (gaussianSmoothD1 s f x) x := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  let A : ℝ → ℝ → F := fun h z =>
    Real.exp ((h / s) * z - (h / s) ^ 2 / 2) • f (x + s * z)
  let A' : ℝ → ℝ → F := fun h z =>
    ((z / s - h / s ^ 2) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) •
      f (x + s * z)
  have hmeas : ∀ᶠ h in nhds (0 : ℝ), AEStronglyMeasurable (A h) (stdGaussian ℝ) := by
    filter_upwards with h
    exact (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hAint : Integrable (A 0) (stdGaussian ℝ) := by
    refine Integrable.mono' (integrable_const ‖f‖)
      (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))).aestronglyMeasurable ?_
    filter_upwards with z
    simpa [A] using f.norm_apply_le (x + s * z)
  have hA'meas : AEStronglyMeasurable (A' 0) (stdGaussian ℝ) :=
    (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(stdGaussian ℝ), ∀ h ∈ Metric.ball (0 : ℝ) 1,
      ‖A' h z‖ ≤ gaussianSmoothD1Dominating s ‖f‖ z := by
    filter_upwards with z
    intro h hh
    change ‖((z / s - h / s ^ 2) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) •
      f (x + s * z)‖ ≤ gaussianSmoothD1Dominating s ‖f‖ z
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (f.norm_apply_le _) (abs_nonneg _)).trans
      (norm_gaussianShiftWeight_deriv_le s ‖f‖ z h hs hh (norm_nonneg f))
  have hdiff : ∀ᵐ z ∂(stdGaussian ℝ), ∀ h ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (A · z) (A' h z) h := by
    filter_upwards with z
    intro h _hh
    exact (hasDerivAt_gaussianShiftWeight s hs0 z h).smul_const (f (x + s * z))
  have hparam :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := A) (F' := A') (bound := gaussianSmoothD1Dominating s ‖f‖)
      (μ := stdGaussian ℝ) (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
      hmeas hAint hA'meas hbound (integrable_gaussianSmoothD1Dominating s ‖f‖ hs) hdiff).2
  have hshift : HasDerivAt (fun h => gaussianSmooth s f (x + h))
      (gaussianSmoothD1 s f x) 0 := by
    have heq : (fun h => gaussianSmooth s f (x + h)) = fun h => ∫ z, A h z ∂(stdGaussian ℝ) := by
      funext h
      simpa [A] using gaussianSmooth_add_eq_integral_exp s hs0 f f.continuous x h
    rw [heq]
    convert hparam using 1
    simp [A', gaussianSmoothD1]
  have hshift' : HasDerivAt (fun h => gaussianSmooth s f (x + h))
      (gaussianSmoothD1 s f x) (x - x) := by simpa using hshift
  have hcomp := hshift'.comp_sub_const x x
  convert hcomp using 1 <;> simp

@[simp]
theorem deriv_gaussianSmooth (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) :
    deriv (gaussianSmooth s f) = gaussianSmoothD1 s f := by
  funext x
  exact (hasDerivAt_gaussianSmooth s hs f x).deriv

private theorem hasDerivAt_gaussianD1ShiftWeight (s : ℝ) (hs : s ≠ 0) (z h : ℝ) :
    HasDerivAt
      (fun r : ℝ => ((z - r / s) / s) *
        Real.exp ((r / s) * z - (r / s) ^ 2 / 2))
      (((((z - h / s) / s) ^ 2 - 1 / s ^ 2) *
        Real.exp ((h / s) * z - (h / s) ^ 2 / 2))) h := by
  have hlin : HasDerivAt (fun r : ℝ => r / s) (1 / s) h :=
    (hasDerivAt_id h).div_const s
  have hpref₀ := ((hasDerivAt_const h z).sub hlin).div_const s
  change HasDerivAt (fun r : ℝ => (z - r / s) / s) _ h at hpref₀
  have hpref : HasDerivAt (fun r : ℝ => (z - r / s) / s) (-1 / s ^ 2) h := by
    convert hpref₀ using 1
    field_simp [hs]
    ring
  have he := hasDerivAt_gaussianShiftWeight s hs z h
  have hout := hpref.mul he
  change HasDerivAt
    (fun r : ℝ => ((z - r / s) / s) * Real.exp ((r / s) * z - (r / s) ^ 2 / 2)) _ h
    at hout
  convert hout using 1
  field_simp [hs]
  ring

private def gaussianSmoothD2Dominating (s C z : ℝ) : ℝ :=
  ((|z| / s + 1 / s ^ 2) ^ 2 + 1 / s ^ 2) * Real.exp ((1 / s) * |z|) * C

private theorem integrable_gaussianSmoothD2Dominating
    (s C : ℝ) (hs : 0 < s) :
    Integrable (gaussianSmoothD2Dominating s C) (stdGaussian ℝ) := by
  have h₀ : Integrable (fun z : ℝ => Real.exp ((1 / s) * |z|)) (stdGaussian ℝ) := by
    simpa [abs_div, abs_of_pos hs] using
      integrable_abs_pow_mul_exp_abs_stdGaussian (1 / s) 0
  have h₁ : Integrable (fun z : ℝ => |z| * Real.exp ((1 / s) * |z|))
      (stdGaussian ℝ) := by
    simpa [abs_div, abs_of_pos hs] using
      integrable_abs_pow_mul_exp_abs_stdGaussian (1 / s) 1
  have h₂ : Integrable (fun z : ℝ => |z| ^ 2 * Real.exp ((1 / s) * |z|))
      (stdGaussian ℝ) := by
    simpa [abs_div, abs_of_pos hs] using
      integrable_abs_pow_mul_exp_abs_stdGaussian (1 / s) 2
  have hout := (((h₂.const_mul (1 / s ^ 2)).add (h₁.const_mul (2 / s ^ 3))).add
    (h₀.const_mul (1 / s ^ 4 + 1 / s ^ 2))).mul_const C
  convert hout using 1
  funext z
  simp only [gaussianSmoothD2Dominating, Pi.add_apply]
  ring

private theorem norm_gaussianD1ShiftWeight_deriv_le
    (s C z h : ℝ) (hs : 0 < s) (hh : h ∈ Metric.ball 0 1) (hC : 0 ≤ C) :
    ‖((((z - h / s) / s) ^ 2 - 1 / s ^ 2) *
      Real.exp ((h / s) * z - (h / s) ^ 2 / 2))‖ * C ≤
      gaussianSmoothD2Dominating s C z := by
  have hah : |h| < 1 := by simpa [Real.dist_eq] using hh
  have hprefEq : (z - h / s) / s = z / s - h / s ^ 2 := by
    field_simp [ne_of_gt hs]
  have hpref : |(z - h / s) / s| ≤ |z| / s + 1 / s ^ 2 := by
    rw [hprefEq]
    calc
      |z / s - h / s ^ 2| ≤ |z / s| + |h / s ^ 2| := by
        simpa using abs_sub_le (z / s) 0 (h / s ^ 2)
      _ = |z| / s + |h| / s ^ 2 := by
        rw [abs_div, abs_div, abs_of_pos hs, abs_of_pos (sq_pos_of_pos hs)]
      _ ≤ |z| / s + 1 / s ^ 2 := by gcongr
  have hcoeff : |((z - h / s) / s) ^ 2 - 1 / s ^ 2| ≤
      (|z| / s + 1 / s ^ 2) ^ 2 + 1 / s ^ 2 := by
    calc
      |((z - h / s) / s) ^ 2 - 1 / s ^ 2| ≤
          |((z - h / s) / s) ^ 2| + |1 / s ^ 2| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (((z - h / s) / s) ^ 2) 0 (1 / s ^ 2)
      _ = |(z - h / s) / s| ^ 2 + 1 / s ^ 2 := by
        rw [abs_pow, abs_of_pos (by positivity : 0 < 1 / s ^ 2)]
      _ ≤ (|z| / s + 1 / s ^ 2) ^ 2 + 1 / s ^ 2 := by
        gcongr
  have hexpArg : (h / s) * z - (h / s) ^ 2 / 2 ≤ (1 / s) * |z| := by
    calc
      (h / s) * z - (h / s) ^ 2 / 2 ≤ (h / s) * z := by
        nlinarith [sq_nonneg (h / s)]
      _ ≤ |(h / s) * z| := le_abs_self _
      _ = (|h| / s) * |z| := by rw [abs_mul, abs_div, abs_of_pos hs]
      _ ≤ (1 / s) * |z| := by gcongr
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  unfold gaussianSmoothD2Dominating
  gcongr

/-- The first differentiated Gaussian kernel differentiates once more, giving the second
Hermite kernel. -/
theorem hasDerivAt_gaussianSmoothD1 (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) (x : ℝ) :
    HasDerivAt (gaussianSmoothD1 s f) (gaussianSmoothD2 s f x) x := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  let B : ℝ → ℝ → F := fun h z =>
    (((z - h / s) / s) * Real.exp ((h / s) * z - (h / s) ^ 2 / 2)) •
      f (x + s * z)
  let B' : ℝ → ℝ → F := fun h z =>
    (((((z - h / s) / s) ^ 2 - 1 / s ^ 2) *
      Real.exp ((h / s) * z - (h / s) ^ 2 / 2))) • f (x + s * z)
  have hmeas : ∀ᶠ h in nhds (0 : ℝ), AEStronglyMeasurable (B h) (stdGaussian ℝ) := by
    filter_upwards with h
    exact (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hdom₀ : Integrable (fun z : ℝ => (|z| / s) * ‖f‖) (stdGaussian ℝ) := by
    have hout := (integrable_abs_stdGaussian.const_mul (1 / s)).mul_const ‖f‖
    convert hout using 1
    funext z
    ring
  have hBint : Integrable (B 0) (stdGaussian ℝ) := by
    refine Integrable.mono' hdom₀
      (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))).aestronglyMeasurable ?_
    filter_upwards with z
    simp only [B, norm_smul, Real.norm_eq_abs]
    norm_num
    rw [abs_div, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (f.norm_apply_le _) (by positivity)
  have hB'meas : AEStronglyMeasurable (B' 0) (stdGaussian ℝ) :=
    (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(stdGaussian ℝ), ∀ h ∈ Metric.ball (0 : ℝ) 1,
      ‖B' h z‖ ≤ gaussianSmoothD2Dominating s ‖f‖ z := by
    filter_upwards with z
    intro h hh
    change ‖(((((z - h / s) / s) ^ 2 - 1 / s ^ 2) *
      Real.exp ((h / s) * z - (h / s) ^ 2 / 2))) • f (x + s * z)‖ ≤
        gaussianSmoothD2Dominating s ‖f‖ z
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (f.norm_apply_le _) (abs_nonneg _)).trans
      (norm_gaussianD1ShiftWeight_deriv_le s ‖f‖ z h hs hh (norm_nonneg f))
  have hdiff : ∀ᵐ z ∂(stdGaussian ℝ), ∀ h ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (B · z) (B' h z) h := by
    filter_upwards with z
    intro h _hh
    exact (hasDerivAt_gaussianD1ShiftWeight s hs0 z h).smul_const (f (x + s * z))
  have hparam :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := B) (F' := B') (bound := gaussianSmoothD2Dominating s ‖f‖)
      (μ := stdGaussian ℝ) (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
      hmeas hBint hB'meas hbound (integrable_gaussianSmoothD2Dominating s ‖f‖ hs) hdiff).2
  have hshift : HasDerivAt (fun h => gaussianSmoothD1 s f (x + h))
      (gaussianSmoothD2 s f x) 0 := by
    have heq : (fun h => gaussianSmoothD1 s f (x + h)) =
        fun h => ∫ z, B h z ∂(stdGaussian ℝ) := by
      funext h
      simpa [B] using gaussianSmoothD1_add_eq_integral_exp s hs0 f f.continuous x h
    rw [heq]
    convert hparam using 1
    simp only [B', gaussianSmoothD2, zero_div, sub_zero, zero_mul, zero_pow,
      OfNat.ofNat_ne_zero, not_false_eq_true, Real.exp_zero, mul_one]
    congr 1
    funext z
    congr 1
    norm_num
    field_simp [hs0]
  have hshift' : HasDerivAt (fun h => gaussianSmoothD1 s f (x + h))
      (gaussianSmoothD2 s f x) (x - x) := by simpa using hshift
  have hcomp := hshift'.comp_sub_const x x
  convert hcomp using 1 <;> simp

@[simp]
theorem deriv_gaussianSmoothD1 (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) :
    deriv (gaussianSmoothD1 s f) = gaussianSmoothD2 s f := by
  funext x
  exact (hasDerivAt_gaussianSmoothD1 s hs f x).deriv

theorem second_deriv_gaussianSmooth (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) :
    deriv (deriv (gaussianSmooth s f)) = gaussianSmoothD2 s f := by
  rw [deriv_gaussianSmooth s hs f, deriv_gaussianSmoothD1 s hs f]

private theorem integrable_gaussianSmoothD1NormDominating (s C : ℝ) (hs : 0 < s) :
    Integrable (fun z : ℝ => (|z| / s) * C) (stdGaussian ℝ) := by
  have hout := (integrable_abs_stdGaussian.const_mul (1 / s)).mul_const C
  convert hout using 1
  funext z
  ring

private theorem integrable_abs_sq_sub_one_stdGaussian :
    Integrable (fun z : ℝ => |z ^ 2 - 1|) (stdGaussian ℝ) := by
  refine (integrable_sq_stdGaussian.sub (integrable_const 1)).norm.congr ?_
  filter_upwards with z
  simp only [Pi.sub_apply, Real.norm_eq_abs]

private theorem integrable_gaussianSmoothD2NormDominating (s C : ℝ) (hs : 0 < s) :
    Integrable (fun z : ℝ => (|z ^ 2 - 1| / s ^ 2) * C) (stdGaussian ℝ) := by
  have hout := (integrable_abs_sq_sub_one_stdGaussian.const_mul (1 / s ^ 2)).mul_const C
  convert hout using 1
  funext z
  ring

/-- Explicit first-derivative estimate at Gaussian scale `s`. -/
theorem norm_gaussianSmoothD1_le (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) (x : ℝ) :
    ‖gaussianSmoothD1 s f x‖ ≤ ‖f‖ / s := by
  have hpoint : ∀ᵐ z ∂(stdGaussian ℝ),
      ‖(z / s) • f (x + s * z)‖ ≤ (|z| / s) * ‖f‖ := by
    filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (f.norm_apply_le _) (by positivity)
  have hnorm := norm_integral_le_of_norm_le
    (integrable_gaussianSmoothD1NormDominating s ‖f‖ hs) hpoint
  rw [gaussianSmoothD1]
  calc
    ‖∫ z, (z / s) • f (x + s * z) ∂(stdGaussian ℝ)‖ ≤
        ∫ z, (|z| / s) * ‖f‖ ∂(stdGaussian ℝ) := hnorm
    _ = ((∫ z, |z| ∂(stdGaussian ℝ)) / s) * ‖f‖ := by
      rw [show (fun z : ℝ => (|z| / s) * ‖f‖) =
          fun z => (1 / s * ‖f‖) * |z| by funext z; ring, integral_const_mul]
      ring
    _ ≤ (1 / s) * ‖f‖ := by
      gcongr
      exact integral_abs_stdGaussian_le_one
    _ = ‖f‖ / s := by ring

/-- Explicit second-derivative estimate at Gaussian scale `s`. -/
theorem norm_gaussianSmoothD2_le (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) (x : ℝ) :
    ‖gaussianSmoothD2 s f x‖ ≤ 2 * ‖f‖ / s ^ 2 := by
  have hpoint : ∀ᵐ z ∂(stdGaussian ℝ),
      ‖((z ^ 2 - 1) / s ^ 2) • f (x + s * z)‖ ≤
        (|z ^ 2 - 1| / s ^ 2) * ‖f‖ := by
    filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hs)]
    exact mul_le_mul_of_nonneg_left (f.norm_apply_le _) (by positivity)
  have hnorm := norm_integral_le_of_norm_le
    (integrable_gaussianSmoothD2NormDominating s ‖f‖ hs) hpoint
  rw [gaussianSmoothD2]
  calc
    ‖∫ z, ((z ^ 2 - 1) / s ^ 2) • f (x + s * z) ∂(stdGaussian ℝ)‖ ≤
        ∫ z, (|z ^ 2 - 1| / s ^ 2) * ‖f‖ ∂(stdGaussian ℝ) := hnorm
    _ = ((∫ z, |z ^ 2 - 1| ∂(stdGaussian ℝ)) / s ^ 2) * ‖f‖ := by
      rw [show (fun z : ℝ => (|z ^ 2 - 1| / s ^ 2) * ‖f‖) =
          fun z => (1 / s ^ 2 * ‖f‖) * |z ^ 2 - 1| by funext z; ring,
        integral_const_mul]
      ring
    _ ≤ (2 / s ^ 2) * ‖f‖ := by
      gcongr
      exact integral_abs_sq_sub_one_stdGaussian_le_two
    _ = 2 * ‖f‖ / s ^ 2 := by ring

/-- The second differentiated kernel is continuous in the spatial variable. -/
theorem continuous_gaussianSmoothD2 (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) :
    Continuous (gaussianSmoothD2 s f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  unfold gaussianSmoothD2
  let D : ℝ → ℝ := fun z => |z ^ 2 - 1| / s ^ 2 * ‖f‖
  have hmeas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable
        (fun z : ℝ => ((z ^ 2 - 1) / s ^ 2) • f (x + s * z)) (stdGaussian ℝ) := by
    filter_upwards with x
    exact (Continuous.smul (by fun_prop) (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hbound : ∀ᶠ x in nhds x₀, ∀ᵐ z ∂(stdGaussian ℝ),
      ‖((z ^ 2 - 1) / s ^ 2) • f (x + s * z)‖ ≤ D z := by
    filter_upwards with x
    filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hs)]
    exact mul_le_mul_of_nonneg_left (f.norm_apply_le _) (by positivity)
  have hlim : ∀ᵐ z ∂(stdGaussian ℝ),
      Tendsto (fun x => ((z ^ 2 - 1) / s ^ 2) • f (x + s * z)) (nhds x₀)
        (nhds (((z ^ 2 - 1) / s ^ 2) • f (x₀ + s * z))) := by
    filter_upwards with z
    exact (Continuous.smul continuous_const (f.continuous.comp (by fun_prop))).tendsto x₀
  exact tendsto_integral_filter_of_dominated_convergence D hmeas hbound
    (integrable_gaussianSmoothD2NormDominating s ‖f‖ hs) hlim

/-- Gaussian convolution of a BUC function is twice continuously differentiable. -/
theorem contDiff_two_gaussianSmooth (s : ℝ) (hs : 0 < s) (f : BUC ℝ F) :
    ContDiff ℝ 2 (gaussianSmooth s f) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_gaussianSmooth s hs f x).differentiableAt, by simp, ?_⟩
  rw [deriv_gaussianSmooth s hs f, contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_gaussianSmoothD1 s hs f x).differentiableAt, ?_⟩
  rw [deriv_gaussianSmoothD1 s hs f]
  exact continuous_gaussianSmoothD2 s hs f

section HeatFlowConsequences

theorem heatScale_pos_of_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    0 < heatScale a t := by
  unfold heatScale
  positivity

/-- Positive-time one-dimensional heat flow is twice continuously differentiable in space. -/
theorem contDiff_two_heatFlow_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC ℝ F) :
    ContDiff ℝ 2 (heatFlow a t f) := by
  rw [heatFlow_real_eq_gaussianSmooth]
  exact contDiff_two_gaussianSmooth (heatScale a t) (heatScale_pos_of_pos ha ht) f

theorem deriv_heatFlow_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC ℝ F) :
    deriv (heatFlow a t f) = gaussianSmoothD1 (heatScale a t) f := by
  rw [heatFlow_real_eq_gaussianSmooth, deriv_gaussianSmooth _ (heatScale_pos_of_pos ha ht) f]

theorem second_deriv_heatFlow_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC ℝ F) :
    deriv (deriv (heatFlow a t f)) = gaussianSmoothD2 (heatScale a t) f := by
  rw [heatFlow_real_eq_gaussianSmooth,
    second_deriv_gaussianSmooth _ (heatScale_pos_of_pos ha ht) f]

/-- Pointwise form of the paper's `L∞` gradient estimate.  Since the right-hand side is the BUC
supremum norm and is independent of `x`, this is a supremum estimate. -/
theorem norm_deriv_heatFlow_real_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) (x : ℝ) :
    ‖deriv (heatFlow a t f) x‖ ≤ ‖f‖ / heatScale a t := by
  rw [deriv_heatFlow_real ha ht f]
  exact norm_gaussianSmoothD1_le _ (heatScale_pos_of_pos ha ht) f x

/-- Pointwise form of the paper's `L∞` Laplacian estimate in one dimension. -/
theorem norm_second_deriv_heatFlow_real_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) (x : ℝ) :
    ‖deriv (deriv (heatFlow a t f)) x‖ ≤ ‖f‖ / (a * t) := by
  rw [second_deriv_heatFlow_real ha ht f]
  calc
    ‖gaussianSmoothD2 (heatScale a t) f x‖ ≤
        2 * ‖f‖ / heatScale a t ^ 2 :=
      norm_gaussianSmoothD2_le _ (heatScale_pos_of_pos ha ht) f x
    _ = ‖f‖ / (a * t) := by
      rw [heatScale_sq ha.le ht.le]
      field_simp [ne_of_gt ha, ne_of_gt ht]

/-- The `sqrt(t)`-weighted gradient bound, with the explicit diffusivity constant from the
Gaussian proof. -/
theorem sqrt_time_mul_norm_deriv_heatFlow_real_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) (x : ℝ) :
    Real.sqrt t * ‖deriv (heatFlow a t f) x‖ ≤ ‖f‖ / Real.sqrt (2 * a) := by
  have hs := heatScale_pos_of_pos ha ht
  have hsa : 0 < Real.sqrt (2 * a) := by positivity
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hscale : heatScale a t = Real.sqrt (2 * a) * Real.sqrt t := by
    unfold heatScale
    rw [show 2 * a * t = (2 * a) * t by ring, Real.sqrt_mul (by positivity)]
  calc
    Real.sqrt t * ‖deriv (heatFlow a t f) x‖ ≤
        Real.sqrt t * (‖f‖ / heatScale a t) :=
      mul_le_mul_of_nonneg_left (norm_deriv_heatFlow_real_le ha ht f x) hst.le
    _ = ‖f‖ / Real.sqrt (2 * a) := by
      rw [hscale]
      field_simp [ne_of_gt hsa, ne_of_gt hst]

/-- The `t`-weighted one-dimensional Laplacian bound, with explicit diffusivity constant. -/
theorem time_mul_norm_second_deriv_heatFlow_real_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) (x : ℝ) :
    t * ‖deriv (deriv (heatFlow a t f)) x‖ ≤ ‖f‖ / a := by
  calc
    t * ‖deriv (deriv (heatFlow a t f)) x‖ ≤ t * (‖f‖ / (a * t)) :=
      mul_le_mul_of_nonneg_left (norm_second_deriv_heatFlow_real_le ha ht f x) ht.le
    _ = ‖f‖ / a := by
      field_simp [ne_of_gt ha, ne_of_gt ht]

end HeatFlowConsequences

end KernelRepresentations

end

end Planarwave
