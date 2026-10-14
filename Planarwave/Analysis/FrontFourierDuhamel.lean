/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierDecomposition
import Planarwave.Analysis.SemigroupParameterContinuity
import Planarwave.Analysis.GaussianFourierDuhamel

/-!
# Duhamel's equation for the full Fourier kernel

The principal and full longitudinal semigroups retain a common Gaussian
frequency weight across the Duhamel time split. This permits frequency-time
Fubini in the longitudinal BUC norm. Spatial convolution and its identification
with the independent spatial evolution remain separate steps.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {m n : ℕ}

local instance : NormedAddCommGroup (BUC ℝ (ℂ^n)) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC ℝ (ℂ^n)) := BUC.instNormedSpace

/-- Joint strong continuity of the principal pencil in frequency, time, and datum. -/
theorem continuous_frontDiffusion_realOrbit_joint (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (c : ℝ) [Nontrivial (ℝ^n)] :
    Continuous (fun p : ℝ × ℝ × BUC ℝ (ℂ^n) ↦
      (frontDiffusionC0Semigroup D hD c p.1).realOrbit p.2.2 p.2.1) := by
  change Continuous (fun p : ℝ × ℝ × BUC ℝ (ℂ^n) ↦
    diffusionBUCCoordinatesEquiv D hD (fun i ↦
      (Real.exp ((-p.1 * diffusionEigenvalues D hD i) * (p.2.1.toNNReal : ℝ)) : ℂ) •
        (complexConvectiveHeatC0Semigroup (diffusionEigenvalues D hD i)
          (diffusionEigenvalues_nonneg D hD i) c).realOrbit
            ((diffusionBUCCoordinatesEquiv D hD).symm p.2.2 i) p.2.1))
  apply (diffusionBUCCoordinatesEquiv D hD).continuous.comp
  apply continuous_pi
  intro i
  have hs : Continuous (fun p : ℝ × ℝ × BUC ℝ (ℂ^n) ↦
      (Real.exp ((-p.1 * diffusionEigenvalues D hD i) * (p.2.1.toNNReal : ℝ)) : ℂ)) := by fun_prop
  have hh : Continuous (fun p : ℝ × ℝ × BUC ℝ (ℂ^n) ↦
      (complexConvectiveHeatC0Semigroup (diffusionEigenvalues D hD i)
        (diffusionEigenvalues_nonneg D hD i) c).realOrbit
          ((diffusionBUCCoordinatesEquiv D hD).symm p.2.2 i) p.2.1) :=
    (C0Semigroup.continuous_realOrbit_joint _).comp (continuous_snd.fst.prodMk
      ((continuous_apply i).comp ((diffusionBUCCoordinatesEquiv D hD).symm.continuous.comp
        continuous_snd.snd)))
  simpa only using! hs.smul hh

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)]

/-- The real-contour symbol is the real-frequency bounded perturbation. -/
theorem frontFourierSemigroupSymbol_embed (t : NNReal) (ξ : ℝ^m) :
    frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) =
      frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ‖ ^ 2) t := by
  rw [frontFourierSemigroupSymbol, complexFrequencyQuadratic_embed,
    frontLinearizedC0Semigroup_eq_pencil]
  norm_cast

/-- The full pencil has joint strong continuity, even where operator-norm time
continuity is unavailable. -/
theorem continuous_frontPencil_realOrbit_joint :
    Continuous (fun p : ℂ × ℝ × BUC ℝ (ℂ^n) ↦
      (frontPencilC0Semigroup f D c φ h₁ h₂ p.1).realOrbit p.2.2 p.2.1) := by
  let S : C0Semigroup ℂ (BUC ℝ (ℂ^n)) := frontLinearizedC0Semigroup f D c φ h₁ h₂ 0
  let A : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) := frontComplexifiedDiffusionBUC D
  have hc₁ : Continuous (fun p : ℂ × ℝ × BUC ℝ (ℂ^n) ↦ -p.1 • A) := by
    simpa only using! (continuous_fst : Continuous
      (fun p : ℂ × ℝ × BUC ℝ (ℂ^n) ↦ p.1)).neg.smul (continuous_const (y := A))
  have hc := hc₁.prodMk continuous_snd
  simpa only [S, A, frontPencilC0Semigroup, Function.comp_def] using!
    S.continuous_boundedPerturbation_realOrbit_joint.comp hc

/-- The two semigroup factors in the real-frequency Duhamel integrand. -/
def frontFourierDuhamelIntegrand (t r : ℝ) (ξ : ℝ^m) (v : BUC ℝ (ℂ^n)) : BUC ℝ (ℂ^n) :=
  (frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2)).realOrbit
    (frontReactionMultiplication f D c φ h₁ h₂
      ((frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖ξ‖ ^ 2)).realOrbit v r)) (t - r)

/-- Joint measurability of the forcing follows from strong joint continuity. -/
theorem continuous_frontFourierDuhamelIntegrand (t : ℝ) (v : BUC ℝ (ℂ^n)) :
    Continuous (fun p : ℝ × ℝ^m ↦ frontFourierDuhamelIntegrand f D c φ h₁ h₂ t p.1 p.2 v) := by
  have hq : Continuous (fun p : ℝ × ℝ^m ↦ (‖p.2‖ ^ 2 : ℝ)) := by fun_prop
  have hT : Continuous (fun p : ℝ × ℝ^m ↦
      (frontLinearizedC0Semigroup f D c φ h₁ h₂ (‖p.2‖ ^ 2)).realOrbit v p.1) := by
    have hp := (continuous_frontPencil_realOrbit_joint f D c φ h₁ h₂).comp
      ((Complex.continuous_ofReal.comp hq).prodMk (continuous_fst.prodMk (continuous_const (y := v))))
    simpa only [Function.comp_def, frontLinearizedC0Semigroup_eq_pencil] using! hp
  let B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) := frontReactionMultiplication f D c φ h₁ h₂
  have hp := (continuous_frontDiffusion_realOrbit_joint D h₁.positive c).comp
    (hq.prodMk (((continuous_const (y := t)).sub continuous_fst).prodMk (B.continuous.comp hT)))
  simpa only [Function.comp_def, frontFourierDuhamelIntegrand, B] using! hp

/-- The full symbol satisfies the original principal-plus-reaction Duhamel equation. -/
theorem frontFourierSemigroupSymbol_duhamel (t : NNReal) (ξ : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) v =
      frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) t v +
        ∫ r in 0..(t : ℝ), frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v := by
  rw [frontFourierSemigroupSymbol_embed]
  let S : C0Semigroup ℂ (BUC ℝ (ℂ^n)) := frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2)
  let B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) := frontReactionMultiplication f D c φ h₁ h₂
  have he : S.perturbedOrbit B v (t : ℝ) = S.realOrbit v (t : ℝ) +
      S.duhamel (fun r ↦ B (S.perturbedOrbit B v r)) (t : ℝ) :=
    S.perturbedOrbit_eq B v t.2
  simpa only [C0Semigroup.perturbedOrbit, C0Semigroup.realOrbit, Real.toNNReal_coe,
    C0Semigroup.duhamel, frontFourierDuhamelIntegrand, frontLinearizedC0Semigroup,
    C0Semigroup.boundedPerturbation_realOrbit, C0Semigroup.boundedPerturbation_apply, S, B] using! he

/-- The time split costs no negative power of either `r` or `t-r`: the two
Gaussian factors retain the decay at total time `t`. -/
theorem exists_frontFourierDuhamelIntegrand_bound :
    ∃ A > 0, ∃ μ > 0, ∃ ω > 0, ∀ (t : ℝ), 0 ≤ t → ∀ r ∈ Icc 0 t,
      ∀ (ξ : ℝ^m) (v : BUC ℝ (ℂ^n)),
        ‖frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v‖ ≤
          A * Real.exp (ω * t) * ‖v‖ * Real.exp (-(μ * t) * ‖ξ‖ ^ 2) := by
  obtain ⟨M, hM, μ, hμ, hb⟩ := exists_uniform_frontDiffusion_bound D h₁.positive h₁.kernel
  let B := frontReactionMultiplication f D c φ h₁ h₂
  let ω := M * ‖B‖ + 1
  refine ⟨M ^ 2 * (‖B‖ + 1), by positivity, μ, hμ, ω, by dsimp [ω]; positivity, ?_⟩
  intro t ht r hr ξ v
  let q := ‖ξ‖ ^ 2
  let S := frontDiffusionC0Semigroup D h₁.positive c q
  have hS : ‖S (t-r).toNNReal‖ ≤ M * Real.exp (-μ * q * (t-r)) := by
    simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr hr.2)] using hb c q (sq_nonneg _) (t-r).toNNReal
  have hT : ‖S.boundedPerturbation B r.toNNReal‖ ≤
      M * Real.exp ((-μ * q + M * ‖B‖) * r) := by
    simpa only [Real.coe_toNNReal _ hr.1] using
      S.norm_boundedPerturbation_le B hM.le (hb c q (sq_nonneg _)) r.toNNReal
  have he : Real.exp (-μ * q * (t-r)) * Real.exp ((-μ * q + M * ‖B‖) * r) =
      Real.exp (M * ‖B‖ * r - μ * q * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change ‖S (t-r).toNNReal (B (S.boundedPerturbation B r.toNNReal v))‖ ≤ _
  calc
    _ ≤ ‖S (t-r).toNNReal‖ * (‖B‖ * (‖S.boundedPerturbation B r.toNNReal‖ * ‖v‖)) := by
      exact ((S _).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((S.boundedPerturbation B _).le_opNorm v) (norm_nonneg B))) (norm_nonneg _))
    _ ≤ (M * Real.exp (-μ * q * (t-r))) *
        (‖B‖ * ((M * Real.exp ((-μ * q + M * ‖B‖) * r)) * ‖v‖)) := by
      gcongr
    _ = M ^ 2 * ‖B‖ * ‖v‖ * Real.exp (M * ‖B‖ * r - μ * q * t) := by
      calc
        _ = M ^ 2 * ‖B‖ * ‖v‖ *
            (Real.exp (-μ * q * (t-r)) * Real.exp ((-μ * q + M * ‖B‖) * r)) := by ring
        _ = _ := by rw [he]
    _ ≤ M ^ 2 * (‖B‖ + 1) * ‖v‖ * Real.exp (ω * t - μ * q * t) := by
      gcongr <;> (try dsimp only [ω]) <;>
        nlinarith [hr.1, hr.2, mul_nonneg hM.le (norm_nonneg B)]
    _ = _ := by
      rw [show ω * t - μ * q * t = ω * t + (-(μ * t) * ‖ξ‖ ^ 2) by dsimp [q]; ring,
        Real.exp_add]
      ring

/-- Absolute integrability of the principal inverse Fourier integral applied
to arbitrary longitudinal BUC data. No transverse integrability is assumed. -/
theorem integrable_frontDiffusion_fourier (t : NNReal) (ht : 0 < t)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    Integrable (fun ξ : ℝ^m ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      (frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) t v)) := by
  obtain ⟨M, hM, μ, hμ, hb⟩ := exists_uniform_frontDiffusion_bound D h₁.positive h₁.kernel
  have hc : Continuous (fun ξ : ℝ^m ↦ frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) t v) := by
    have hh := (continuous_frontDiffusion_realOrbit_joint D h₁.positive c).comp
      (((continuous_norm : Continuous (fun ξ : ℝ^m ↦ ‖ξ‖)).pow 2).prodMk ((continuous_const (y := (t : ℝ))).prodMk
        (continuous_const (y := v))))
    simpa only [Function.comp_def, C0Semigroup.realOrbit, Real.toNNReal_coe] using! hh
  apply integrable_oscillatory_of_gaussian_bound hc (mul_pos hμ ht) (C := M * ‖v‖) _ x
  intro ξ
  calc
    _ ≤ ‖frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) t‖ * ‖v‖ :=
      (frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) t).le_opNorm v
    _ ≤ (M * Real.exp (-μ * ‖ξ‖ ^ 2 * t)) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hb c _ (sq_nonneg _) t) (norm_nonneg v)
    _ = _ := by
      ring_nf
      exact mul_right_comm M _ _

/-- Joint absolute convergence of the actual frequency-space forcing, uniformly
through both endpoints of the time split. -/
theorem integrable_frontFourierDuhamel_time_frequency (t : NNReal) (ht : 0 < t)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    Integrable (fun p : ℝ × ℝ^m ↦ Complex.exp (Complex.I * (⟪p.2, x⟫ : ℂ)) •
      frontFourierDuhamelIntegrand f D c φ h₁ h₂ t p.1 p.2 v)
      ((volume.restrict (Ioc 0 (t : ℝ))).prod volume) := by
  obtain ⟨A, _, μ, hμ, ω, _, hb⟩ := exists_frontFourierDuhamelIntegrand_bound (m := m) f D c φ h₁ h₂
  exact integrable_time_oscillatory_of_gaussian_bound
    (continuous_frontFourierDuhamelIntegrand f D c φ h₁ h₂ t v) (mul_pos hμ ht)
    (fun r hr ξ ↦ hb t t.2 r hr ξ v) x

/-- Fourier inversion commutes with the actual longitudinal Duhamel time integral. -/
theorem frontFourierDuhamel_frequency_time_swap (t : NNReal) (ht : 0 < t)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    (∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      ∫ r in 0..(t : ℝ), frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v) =
      ∫ r in 0..(t : ℝ), ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
        frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v := by
  obtain ⟨A, _, μ, hμ, ω, _, hb⟩ := exists_frontFourierDuhamelIntegrand_bound (m := m) f D c φ h₁ h₂
  exact oscillatoryIntegral_intervalIntegral_swap
    (continuous_frontFourierDuhamelIntegrand f D c φ h₁ h₂ t v) (mul_pos hμ ht) t.2
    (fun r hr ξ ↦ hb t t.2 r hr ξ v) x

/-- The inverse Fourier transform of the Duhamel forcing is integrable in time
as a longitudinal BUC value. -/
theorem intervalIntegrable_frontFourierDuhamel_inverse (t : NNReal) (ht : 0 < t)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    IntervalIntegrable (fun r ↦ ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v) volume 0 t := by
  obtain ⟨A, _, μ, hμ, ω, _, hb⟩ := exists_frontFourierDuhamelIntegrand_bound (m := m) f D c φ h₁ h₂
  exact intervalIntegrable_oscillatoryIntegral_of_gaussian_bound
    (continuous_frontFourierDuhamelIntegrand f D c φ h₁ h₂ t v) (mul_pos hμ ht) t.2
    (fun r hr ξ ↦ hb t t.2 r hr ξ v) x

/-- Applying inverse Fourier transformation to the longitudinal Duhamel equation
is legitimate in BUC, and puts the time integral outside the frequency integral. -/
theorem frontFourierSemigroup_inverse_duhamel (t : NNReal) (ht : 0 < t)
    (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    (∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      (frontFourierSemigroupSymbol f D c φ h₁ h₂ t (embed ξ) v)) =
      (∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
        (frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) t v)) +
      ∫ r in 0..(t : ℝ), ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
        frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v := by
  have hi : Integrable (fun ξ : ℝ^m ↦ Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
      ∫ r in 0..(t : ℝ), frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v) := by
    simp_rw [← intervalIntegral.integral_smul,
      intervalIntegral.integral_of_le (show 0 ≤ (t : ℝ) from t.2)]
    exact (integrable_frontFourierDuhamel_time_frequency f D c φ h₁ h₂ t ht x v).integral_prod_right
  simp_rw [frontFourierSemigroupSymbol_duhamel, smul_add]
  rw [integral_add (integrable_frontDiffusion_fourier f D c h₁ t ht x v) hi,
    frontFourierDuhamel_frequency_time_swap f D c φ h₁ h₂ t ht x v]

/-- The full normalized Fourier kernel satisfies the inverse-transformed
Duhamel identity. This is a kernel identity, not yet a spatial semigroup identity. -/
theorem frontFourierKernel_duhamel (ψ : ℝ → ℝ^n)
    (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)
    (t : NNReal) (ht : 0 < t) (x : ℝ^m) (v : BUC ℝ (ℂ^n)) :
    frontFourierKernel f D c φ h₁ h₂ t x v =
      ((2 * Real.pi) ^ m)⁻¹ •
        (∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
          (frontDiffusionC0Semigroup D h₁.positive c (‖ξ‖ ^ 2) t v)) +
      ∫ r in 0..(t : ℝ), ((2 * Real.pi) ^ m)⁻¹ •
        ∫ ξ : ℝ^m, Complex.exp (Complex.I * (⟪ξ, x⟫ : ℂ)) •
          frontFourierDuhamelIntegrand f D c φ h₁ h₂ t r ξ v := by
  rw [frontFourierKernel_apply f D c φ h₁ h₂ ψ h₃ t ht,
    frontFourierSemigroup_inverse_duhamel f D c φ h₁ h₂ t ht x v,
    smul_add, intervalIntegral.integral_smul]

end

end Planarwave
