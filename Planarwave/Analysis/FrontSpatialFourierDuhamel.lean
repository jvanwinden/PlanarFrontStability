/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.SpatialDiffusionFourier

/-!
# The spatial Duhamel equation in transverse Fourier coordinates

Slicing intertwines the actual spatial reaction multiplication with the
longitudinal reaction multiplication in the Fourier pencil. The independently
constructed full spatial evolution therefore satisfies Duhamel's equation with
the proved principal Fourier integral. Identifying its solution with the full
longitudinal-semigroup Fourier integral remains a separate obligation.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-- Strong continuity is sufficient for the Duhamel integrand; operator-norm
continuity of the semigroup at time zero is not required. -/
theorem continuous_duhamel_two_semigroups {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (S T : C0Semigroup ℂ E)
    (B : E →L[ℂ] E) (v : E) (t : ℝ) :
    Continuous (fun r : ℝ ↦ S.realOrbit (B (T.realOrbit v r)) (t - r)) :=
  (S.continuous_duhamel_integrand (B.continuous.comp (T.continuous_realOrbit v))).comp
    (continuous_const.prodMk continuous_id)

variable {d m n : ℕ}

local instance : NormedAddCommGroup (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedAddCommGroup
local instance : NormedSpace ℂ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace
local instance : NormedSpace ℝ (BUC (ℝ^m) (BUC ℝ (ℂ^n))) := BUC.instNormedSpace

/-- The real front coefficient is the same longitudinal multiplication on every slice. -/
theorem spatialSlices_frontReaction (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
    (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
    (hd : 2 ≤ d) (v : BUC (ℝ^d) (ℂ^n)) :
    spatialSlices hd (frontSpatialReactionMultiplication f D c φ h₁ h₂ hd v) =
      BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂) (spatialSlices hd v) := by
  apply BUC.ext
  intro y
  apply BUC.ext
  intro z
  change (complexFrontDerivativeCoefficient f D c φ h₁ h₂) (horizontal (full y z))
      (v (full y z)) = (complexFrontDerivativeCoefficient f D c φ h₁ h₂) z (v (full y z))
  rw [horizontal_full hd]

variable [Nontrivial (ℝ^n)]

/-- The iterated principal Fourier integral. Its evolution interpretation below
is for positive time only; no assertion about this integral at time zero is used. -/
def diffusionFourierIntegral (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (c : ℝ)
    (t : NNReal) (v : BUC (ℝ^m) (BUC ℝ (ℂ^n))) (y : ℝ^m) : BUC ℝ (ℂ^n) :=
  ((2 * Real.pi) ^ m)⁻¹ • ∫ y' : ℝ^m, ∫ ξ : ℝ^m,
    Complex.exp (Complex.I * (⟪ξ, y - y'⟫ : ℂ)) •
      (frontDiffusionC0Semigroup D hD c (‖ξ‖ ^ 2) t (v y'))

/-- The principal Fourier integral agrees with the independently constructed
spatial semigroup on every actual spatial BUC datum. -/
theorem diffusionFourierIntegral_spatialSlices (hd : 2 ≤ d) (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (hDinj : Function.Injective D) (c : ℝ)
    (t : NNReal) (ht : 0 < t) (v : BUC (ℝ^d) (ℂ^n)) (y : ℝ^(d - 1)) :
    diffusionFourierIntegral D hD c t (spatialSlices hd v) y =
      spatialSlices hd (spatialDiffusionC0Semigroup D hD (frontSpatialDrift hd c) t v) y :=
  (spatialDiffusionC0Semigroup_eq_fourierIntegral hd D hD hDinj c t ht v y).symm

/-- Exact Duhamel formula for the full spatial semigroup with its principal
evolution replaced by the transverse Fourier integral. The zero-lag endpoint
is discarded only as a null singleton in the time integral. -/
theorem frontSpatialC0Semigroup_fourier_duhamel (f : ℝ^n → ℝ^n)
    (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ : ℝ → ℝ^n)
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (hd : 2 ≤ d)
    (t : NNReal) (ht : 0 < t) (v : BUC (ℝ^d) (ℂ^n)) (y : ℝ^(d - 1)) :
    spatialSlices hd (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) y =
      diffusionFourierIntegral D h₁.positive c t (spatialSlices hd v) y +
        ∫ r in 0..(t : ℝ), diffusionFourierIntegral D h₁.positive c ((t : ℝ) - r).toNNReal
          (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
            (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r))) y := by
  let S : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) :=
    spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)
  let T : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) := frontSpatialC0Semigroup f D c φ h₁ h₂ hd
  let B : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n) :=
    frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
  let U : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    (BUC.evalCLM (𝕜 := ℂ) y).comp (spatialSlicesCLM ℂ hd)
  have hc : Continuous (fun r : ℝ ↦ S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r)) :=
    continuous_duhamel_two_semigroups S T B v t
  have hm := congrArg U (frontSpatialC0Semigroup_mild f D c φ h₁ h₂ hd v t.2)
  change U (T.realOrbit v t) = U (S.realOrbit v t + S.duhamel (fun r ↦ B (T.realOrbit v r)) t) at hm
  rw [map_add, C0Semigroup.duhamel, ← U.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)] at hm
  have hfree : U (S.realOrbit v t) = diffusionFourierIntegral D h₁.positive c t (spatialSlices hd v) y := by
    simpa only [U, S, ContinuousLinearMap.comp_apply, BUC.evalCLM_apply, spatialSlicesCLM_apply,
      C0Semigroup.realOrbit_coe] using!
      (diffusionFourierIntegral_spatialSlices hd D h₁.positive h₁.kernel c t ht v y).symm
  have htime : (∫ r in 0..(t : ℝ), U (S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r))) =
      ∫ r in 0..(t : ℝ), diffusionFourierIntegral D h₁.positive c ((t : ℝ) - r).toNNReal
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
          (spatialSlices hd (T.realOrbit v r))) y := by
    apply intervalIntegral.integral_congr_Ioo_of_le t.2
    intro r hr
    have htr : 0 < ((t : ℝ) - r).toNNReal := Real.toNNReal_pos.mpr (sub_pos.mpr hr.2)
    dsimp only
    rw [← spatialSlices_frontReaction f D c φ h₁ h₂ hd,
      diffusionFourierIntegral_spatialSlices hd D h₁.positive h₁.kernel c _ htr]
    rfl
  rw [hfree, htime] at hm
  simpa only [U, T, ContinuousLinearMap.comp_apply, BUC.evalCLM_apply, spatialSlicesCLM_apply,
    C0Semigroup.realOrbit_coe] using! hm

/-- The time integral in the Fourier-form Duhamel equation is absolutely
integrable in longitudinal BUC, including its possibly singular zero-lag endpoint. -/
theorem intervalIntegrable_frontSpatial_fourier_forcing (f : ℝ^n → ℝ^n)
    (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ) (φ : ℝ → ℝ^n)
    (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (hd : 2 ≤ d)
    (t : NNReal) (v : BUC (ℝ^d) (ℂ^n)) (y : ℝ^(d - 1)) :
    IntervalIntegrable (fun r : ℝ ↦
      diffusionFourierIntegral D h₁.positive c ((t : ℝ) - r).toNNReal
        (BUC.postcompCLM (frontReactionMultiplication f D c φ h₁ h₂)
          (spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r))) y)
      volume 0 t := by
  let S : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) :=
    spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)
  let T : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) := frontSpatialC0Semigroup f D c φ h₁ h₂ hd
  let B : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n) :=
    frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
  let U : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
    (BUC.evalCLM (𝕜 := ℂ) y).comp (spatialSlicesCLM ℂ hd)
  have hc : Continuous (fun r : ℝ ↦ S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r)) :=
    continuous_duhamel_two_semigroups S T B v t
  have hi : IntervalIntegrable (fun r : ℝ ↦
      U (S.realOrbit (B (T.realOrbit v r)) ((t : ℝ) - r))) volume 0 t :=
    (U.continuous.comp hc).intervalIntegrable 0 t
  apply hi.congr_uIoo
  intro r hr
  have hr' : r ∈ Ioo 0 (t : ℝ) := uIoo_of_le t.2 ▸ hr
  have htr : 0 < ((t : ℝ) - r).toNNReal := Real.toNNReal_pos.mpr (sub_pos.mpr hr'.2)
  dsimp only
  rw [← spatialSlices_frontReaction f D c φ h₁ h₂ hd,
    diffusionFourierIntegral_spatialSlices hd D h₁.positive h₁.kernel c _ htr]
  rfl

end

end Planarwave
