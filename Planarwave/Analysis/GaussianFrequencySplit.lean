/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.GaussianFourierKernel

@[expose] public section

/-!
# Integrating the three-term frequency split

The on-diagonal proof separates the high-frequency tail, the low-frequency
complement, and the critical Taylor remainder. Their positive majorants may
be integrated over the whole frequency space except for the constant
complementary bound, which is integrated only over the finite low-frequency ball.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedSpace ℂ F] in
/-- Integrate the outside contribution, the constant inside contribution, and
the remaining inside contribution separately. -/
theorem integral_norm_le_threeTerm {g : V → F} (hg : Integrable g)
    {s : Set V} (hs : MeasurableSet s) (hvol : volume s ≠ ⊤)
    {C : ℝ} {u v : V → ℝ} (hu : Integrable u) (hv : Integrable v)
    (hu₀ : ∀ ξ, 0 ≤ u ξ) (hv₀ : ∀ ξ, 0 ≤ v ξ)
    (hout : ∀ ξ, ξ ∉ s → ‖g ξ‖ ≤ u ξ)
    (hin : ∀ ξ, ξ ∈ s → ‖g ξ‖ ≤ C + v ξ) :
    (∫ ξ, ‖g ξ‖) ≤ (∫ ξ, u ξ) + volume.real s * C + ∫ ξ, v ξ := by
  have hC : Integrable (s.indicator (fun _ : V ↦ C)) :=
    (integrable_indicator_iff hs).mpr (integrableOn_const (C := C) hvol)
  have hp (ξ : V) : ‖g ξ‖ ≤ u ξ + s.indicator (fun _ : V ↦ C) ξ + v ξ := by
    by_cases hξ : ξ ∈ s
    · rw [indicator_of_mem hξ]
      linarith [hin ξ hξ, hu₀ ξ]
    · rw [indicator_of_notMem hξ]
      linarith [hout ξ hξ, hv₀ ξ]
  apply (integral_mono hg.norm ((hu.add hC).add hv) hp).trans_eq
  calc
    (∫ ξ, ((u + s.indicator (fun _ ↦ C)) + v) ξ) =
        (∫ ξ, (u + s.indicator (fun _ ↦ C)) ξ) + ∫ ξ, v ξ := integral_add (hu.add hC) hv
    _ = _ := by
      rw [show (∫ ξ, (u + s.indicator (fun _ ↦ C)) ξ) =
        (∫ ξ, u ξ) + ∫ ξ, s.indicator (fun _ ↦ C) ξ from integral_add hu hC]
      rw [integral_indicator_const C hs, smul_eq_mul]

/-- The integrated form of the paper's three Gaussian/exponential frequency estimates. -/
theorem norm_oscillatoryIntegral_le_threeTerm {g : V → F} (hg : Integrable g)
    {s : Set V} (hs : MeasurableSet s) (hvol : volume s ≠ ⊤)
    {A B C b d : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hb : 0 < b) (hd : 0 < d)
    (hout : ∀ ξ, ξ ∉ s → ‖g ξ‖ ≤ C * Real.exp (-d * ‖ξ‖ ^ 2))
    (hin : ∀ ξ, ξ ∈ s → ‖g ξ‖ ≤ A + B * Real.exp (-b * ‖ξ‖ ^ 2)) (x : V) :
    ‖oscillatoryIntegral g x‖ ≤
      C * (Real.pi / d) ^ (Module.finrank ℝ V / 2 : ℝ) + volume.real s * A +
        B * (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ) := by
  calc
    ‖oscillatoryIntegral g x‖ ≤ ∫ ξ, ‖g ξ‖ := by
      simpa only [oscillatoryIntegral, norm_oscillatoryIntegrand] using!
        (norm_integral_le_integral_norm (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ ξ x : ℂ)) • g ξ))
    _ ≤ _ := by
      have h := integral_norm_le_threeTerm hg hs hvol
        ((integrable_gaussian_norm hd).const_mul C) ((integrable_gaussian_norm hb).const_mul B)
        (fun ξ ↦ by positivity) (fun ξ ↦ by positivity) hout hin
      simpa only [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb,
        GaussianFourier.integral_rexp_neg_mul_sq_norm hd] using h

end

end Planarwave
