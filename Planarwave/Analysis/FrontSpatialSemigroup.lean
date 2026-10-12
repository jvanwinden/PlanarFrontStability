/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.SpatialDiffusionSemigroup
import all Planarwave.Analysis.FrontLinearizedMild
import all Planarwave.Coordinates
import Planarwave.Analysis.SemigroupPerturbationGenerator
import Planarwave.Analysis.SemigroupPerturbationBound

/-!
# The full spatial linearized front semigroup

Construct the semigroup on the actual full spatial BUC space: first matrix
diffusion with the longitudinal drift, then multiplication by `f'(φ(z))`.
This construction does not assume a Fourier representation or a remainder
decomposition. The Duhamel identity and the generator perturbation identity
will be used to identify that representation.
-/

open Set

namespace Planarwave

noncomputable section

set_option synthInstance.maxHeartbeats 200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

/-- The challenge's longitudinal coordinate as a bounded linear functional. -/
def horizontalCLM {d : ℕ} (hd : 2 ≤ d) : ℝ^d →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (ℝ^(d - 1)) ℝ).comp (coordinateEquiv hd).toContinuousLinearMap

@[simp]
theorem horizontalCLM_apply {d : ℕ} (hd : 2 ≤ d) (x : ℝ^d) : horizontalCLM hd x = horizontal x := rfl

/-- The physical drift vector has zero transverse part and longitudinal component `c`. -/
def frontSpatialDrift {d : ℕ} (hd : 2 ≤ d) (c : ℝ) : ℝ^d :=
  (coordinateEquiv hd).symm (0, c)

@[simp]
theorem frontSpatialDrift_coordinates {d : ℕ} (hd : 2 ≤ d) (c : ℝ) :
    coordinateEquiv hd (frontSpatialDrift hd c) = (0, c) := (coordinateEquiv hd).apply_symm_apply _

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (hd : 2 ≤ d)

/-- The actual reaction coefficient extended constantly in the transverse coordinates. -/
def frontSpatialReactionMultiplication : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n) :=
  BUC.operatorApplyCLM
    ((complexFrontDerivativeCoefficient f D c φ h₁ h₂).comp (horizontalCLM hd) (horizontalCLM hd).uniformContinuous)

/-- Pointwise identification with the linearized reaction term in the PDE. -/
theorem frontSpatialReactionMultiplication_apply (v : BUC (ℝ^d) (ℂ^n)) (x : ℝ^d) :
    frontSpatialReactionMultiplication f D c φ h₁ h₂ hd v x =
      (fderiv ℝ f (φ (horizontal x))).complexify (v x) :=
  complexFrontDerivativeCoefficient_apply f D c φ h₁ h₂ (horizontal x) (v x)

/-- The bounded perturbation costs no extra spatial dependence in its norm bound. -/
theorem norm_frontSpatialReactionMultiplication_le :
    ‖frontSpatialReactionMultiplication f D c φ h₁ h₂ hd‖ ≤
      ‖complexFrontDerivativeCoefficient f D c φ h₁ h₂‖ := by
  let A := complexFrontDerivativeCoefficient f D c φ h₁ h₂
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  change ‖A (horizontal x) (v x)‖ ≤ _
  exact ((A (horizontal x)).le_opNorm (v x)).trans
    (mul_le_mul (A.norm_apply_le _) (v.norm_apply_le _) (norm_nonneg _) (norm_nonneg _))

variable [Nontrivial (ℝ^n)]

/-- The full spatial linearized evolution, independently constructed by bounded perturbation. -/
def frontSpatialC0Semigroup : C0Semigroup ℂ (BUC (ℝ^d) (ℂ^n)) :=
  (spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)).boundedPerturbation
    (frontSpatialReactionMultiplication f D c φ h₁ h₂ hd)

/-- Exact full-domain perturbation identity for the spatial generator. -/
theorem frontSpatialC0Semigroup_hasGeneratorAt_iff (v w : BUC (ℝ^d) (ℂ^n)) :
    (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).HasGeneratorAt v w ↔
      (spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)).HasGeneratorAt v
        (w - frontSpatialReactionMultiplication f D c φ h₁ h₂ hd v) :=
  C0Semigroup.boundedPerturbation_hasGeneratorAt_iff _ _ v w

/-- The spatial generator on twice BUC differentiable diffusion-coordinate data. -/
theorem frontSpatialC0Semigroup_hasGeneratorAt
    (v : Fin n → BUC (ℝ^d) ℂ) (g : Fin n → BUC (ℝ^d) (ℝ^d →L[ℝ] ℂ))
    (h : Fin n → BUC (ℝ^d) (ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℂ))
    (hg : ∀ i x, HasFDerivAt (v i) (g i x) x) (hh : ∀ i x, HasFDerivAt (g i) (h i x) x) :
    (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).HasGeneratorAt
      (spatialDiffusionBUCCoordinatesEquiv D h₁.positive v)
      (spatialDiffusionBUCCoordinatesEquiv D h₁.positive
        (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D h₁.positive i)
          (frontSpatialDrift hd c) (g i) (h i)) +
        frontSpatialReactionMultiplication f D c φ h₁ h₂ hd (spatialDiffusionBUCCoordinatesEquiv D h₁.positive v)) :=
  (spatialDiffusionC0Semigroup_hasGeneratorAt D h₁.positive h₁.kernel (frontSpatialDrift hd c) v g h hg hh).boundedPerturbation _

/-- The full spatial Duhamel identity used to recover the Fourier representation. -/
theorem frontSpatialC0Semigroup_mild (v : BUC (ℝ^d) (ℂ^n)) {t : ℝ} (ht : 0 ≤ t) :
    (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v t =
      (spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)).realOrbit v t +
        (spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)).duhamel
          (fun r ↦ frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
            ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit v r)) t :=
  C0Semigroup.perturbedOrbit_eq _ _ v ht

/-- A global exponential norm bound for the independently constructed spatial semigroup. -/
theorem exists_frontSpatialC0Semigroup_bound :
    ∃ M > 0, ∃ ω > 0, ∀ t : NNReal,
      ‖frontSpatialC0Semigroup f D c φ h₁ h₂ hd t‖ ≤ M * Real.exp (ω * t) := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_spatialDiffusion_bound (E := ℝ^d) D h₁.positive
  let B := frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
  refine ⟨M, hM, M * ‖B‖ + 1, by positivity, ?_⟩
  intro t
  have h := (spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)).norm_boundedPerturbation_le B
    (ω := 0) hM.le (by intro r; simpa using hbound (frontSpatialDrift hd c) r) t
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  nlinarith [t.2]

/-- The short-time uniform bound invoked in the last paragraph of Section 3. -/
theorem exists_frontSpatialC0Semigroup_shortTime_bound :
    ∃ C > 0, ∀ t : NNReal, t ≤ 1 → ‖frontSpatialC0Semigroup f D c φ h₁ h₂ hd t‖ ≤ C := by
  obtain ⟨M, hM, ω, hω, hb⟩ := exists_frontSpatialC0Semigroup_bound f D c φ h₁ h₂ hd
  refine ⟨M * Real.exp ω, by positivity, ?_⟩
  intro t ht
  apply (hb t).trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ 1 from ht) hω.le).trans_eq (mul_one _)

end

end Planarwave
