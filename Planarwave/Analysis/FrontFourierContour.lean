/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontFourierKernel
import Planarwave.Analysis.FourierContourShift
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The remainder kernel is independent of the Fourier contour

Apply the coordinatewise Cauchy argument to the entire remainder symbol and its
Gaussian bounds from Lemma 2.2. The volume-preserving Euclidean/product coordinate
identification transfers the result to the kernel defined in Section 3.
-/

open MeasureTheory
open scoped InnerProductSpace ContDiff

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-- Product-coordinate and Euclidean-coordinate descriptions of the same contour. -/
theorem toLp_piContourPoint {m : ℕ} (ξ η : Fin m → ℝ) :
    WithLp.toLp 2 (piContourPoint ξ η) =
      complexFrequencyShift (WithLp.toLp 2 ξ) (WithLp.toLp 2 η) := by
  ext i
  simp [piContourPoint, complexFrequencyShift_apply, mul_comm]

/-- The product-coordinate real pairing is the Euclidean real inner product. -/
theorem sum_mul_eq_real_inner {m : ℕ} (ξ x : ℝ^m) :
    (∑ i, ξ i * x i) = ⟪ξ, x⟫_ℝ := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

local instance : NormSMulClass ℂ (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) := by
  exact NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))

/-- The product-coordinate contour integral is exactly the previously defined shifted kernel. -/
theorem integral_piFourier_front_eq_shiftedKernel (t : NNReal) (η x : ℝ^m) :
    (∫ ξ : Fin m → ℝ,
      piFourierPhase x.ofLp (piContourPoint ξ η.ofLp) •
        frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t
          (WithLp.toLp 2 (piContourPoint ξ η.ofLp))) =
      frontShiftedRemainderKernel f D c φ h₁ h₂ ψ h₃ t η x := by
  simp_rw [piFourierPhase_shift, toLp_piContourPoint]
  change (∫ ξ : Fin m → ℝ,
    (Complex.exp (-(∑ i, η i * x i : ℝ)) * Complex.exp (Complex.I * (∑ i, ξ i * x i : ℝ))) •
      frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t
        (complexFrequencyShift (WithLp.toLp 2 ξ) η)) = _
  have hmul (a b : ℂ) (A : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :
      (a * b) • A = a • b • A := mul_smul a b A
  simp_rw [hmul]
  rw [sum_mul_eq_real_inner η x]
  rw [integral_smul (𝕜 := ℂ) (G := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))]
  unfold frontShiftedRemainderKernel oscillatoryIntegral
  congr 1
  have he := (PiLp.volume_preserving_toLp (Fin m)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding
    (fun ξ : ℝ^m ↦ Complex.exp (Complex.I * (⟪ξ, x⟫_ℝ : ℂ)) •
      frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (complexFrequencyShift ξ η))
  simpa only [← sum_mul_eq_real_inner] using! he

/-- The paper's Cauchy identity: every shifted Fourier kernel equals the original real-contour kernel.
The entire symbol and Gaussian bounds discharge all analytic hypotheses of Cauchy's theorem. -/
theorem frontShiftedRemainderKernel_eq (t : NNReal) (ht : 0 < t) (η x : ℝ^m) :
    frontShiftedRemainderKernel f D c φ h₁ h₂ ψ h₃ t η x =
      frontRemainderKernel f D c φ h₁ h₂ ψ h₃ t x := by
  let g : (Fin m → ℂ) → (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)) :=
    fun ζ ↦ frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (WithLp.toLp 2 ζ)
  have hg : ContDiff ℂ ω g :=
    (contDiff_frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t).comp PiLp.contDiff_toLp
  obtain ⟨M, hM, μ, hμ, κ, hκ, hb⟩ := exists_frontFourierRemainderSymbol_bound (m := m) f D c φ h₁ h₂ ψ h₃
  have hbound (ζ : Fin m → ℂ) : ‖g ζ‖ ≤
      (M * Real.exp (κ * t)) * Real.exp
        (-(μ * t) * ∑ i, (ζ i).re ^ 2 + (κ * t) * ∑ i, (ζ i).im ^ 2) := by
    let ξ : ℝ^m := WithLp.toLp 2 (fun i ↦ (ζ i).re)
    let η' : ℝ^m := WithLp.toLp 2 (fun i ↦ (ζ i).im)
    have heq : WithLp.toLp 2 ζ = complexFrequencyShift ξ η' := by
      ext i
      simpa only [complexFrequencyShift_apply, ξ, η'] using
        ((ζ i).re_add_im.symm.trans (by rw [mul_comm (↑(ζ i).im) Complex.I]))
    change ‖frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (WithLp.toLp 2 ζ)‖ ≤ _
    rw [heq]
    apply (hb ξ η' t).trans_eq
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [ξ, η']
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h := integral_piFourierContour_eq (F := BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n))
    (by positivity : 0 ≤ M * Real.exp (κ * t)) (mul_pos hμ ht) (mul_nonneg hκ.le t.2)
    (hg.differentiable (by simp)) hbound x.ofLp η.ofLp (0 : ℝ^m).ofLp
  change (∫ ξ, piFourierPhase x.ofLp (piContourPoint ξ η.ofLp) •
    frontFourierRemainderSymbol f D c φ h₁ h₂ ψ h₃ t (WithLp.toLp 2 (piContourPoint ξ η.ofLp))) = _ at h
  rw [integral_piFourier_front_eq_shiftedKernel] at h
  exact h.trans (integral_piFourier_front_eq_shiftedKernel f D c φ h₁ h₂ ψ h₃ t 0 x)

end

end Planarwave
