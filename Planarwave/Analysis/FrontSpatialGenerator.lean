/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSpatialSemigroup

/-!
# Identification of the spatial linearized generator

Return from diffusion eigenvector coordinates and identify the generator
pointwise with `D Δ + c ∂z + f'(φ(z))`. The generator relation itself is a
supremum-norm right derivative, not just a pointwise differentiation claim.
-/

open Filter Set Topology
open scoped Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

section Regularity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two continuous specified Fréchet derivatives give `C²` regularity. -/
theorem contDiff_two_of_buc_fderivatives (v : BUC E F) (g : BUC E (E →L[ℝ] F))
    (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hg : ∀ x, HasFDerivAt v (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) :
    ContDiff ℝ 2 (v : E → F) := by
  have hvg : fderiv ℝ v = g := funext fun x ↦ (hg x).fderiv
  have hgh : fderiv ℝ g = h := funext fun x ↦ (hh x).fderiv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun x ↦ (hg x).differentiableAt, by simp, ?_⟩
  rw [hvg, contDiff_one_iff_fderiv, hgh]
  exact ⟨fun x ↦ (hh x).differentiableAt, h.continuous⟩

end Regularity

variable {n : ℕ}

section Principal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- In original state coordinates the diagonal generator is precisely matrix
diffusion plus the common drift. -/
theorem spatialDiffusionGenerator_coordinates (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (b : E) (v : Fin n → BUC E ℂ) (g : Fin n → BUC E (E →L[ℝ] ℂ))
    (h : Fin n → BUC E (E →L[ℝ] E →L[ℝ] ℂ))
    (hg : ∀ i x, HasFDerivAt (v i) (g i x) x) (hh : ∀ i x, HasFDerivAt (g i) (h i x) x) (x : E) :
    spatialDiffusionBUCCoordinatesEquiv D hD
        (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D hD i) b (g i) (h i)) x =
      frontComplexifiedDiffusion D (Δ (spatialDiffusionBUCCoordinatesEquiv D hD v : E → ℂ^n) x) +
        fderiv ℝ (spatialDiffusionBUCCoordinatesEquiv D hD v) x b := by
  let J := diffusionCoordinatesEquiv D hD
  let u : E → Fin n → ℂ := fun y i ↦ v i y
  have hu : ContDiff ℝ 2 u := contDiff_pi.mpr fun i ↦ contDiff_two_of_buc_fderivatives (v i) (g i) (h i) (hg i) (hh i)
  have hΔ : Δ (spatialDiffusionBUCCoordinatesEquiv D hD v : E → ℂ^n) x = J (Δ u x) := by
    exact hu.contDiffAt.laplacian_CLM_comp_left (l := J.toContinuousLinearMap.restrictScalars ℝ)
  have hΔi (i : Fin n) : Δ (v i : E → ℂ) x = (Δ u x) i := by
    exact hu.contDiffAt.laplacian_CLM_comp_left
      (l := (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)
  have hderiv := (J.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
    (hasFDerivAt_pi.mpr (fun i ↦ hg i x))
  have hd : fderiv ℝ (spatialDiffusionBUCCoordinatesEquiv D hD v) x b =
      J (fun i ↦ g i x b) := by
    exact congrArg (fun L : E →L[ℝ] ℂ^n ↦ L b) hderiv.fderiv
  rw [hΔ, hd, complexifiedDiffusion_coordinates]
  rw [← J.map_add]
  change J (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D hD i) b (g i) (h i) x) = _
  congr 1
  funext i
  rw [convectiveGeneratorBUC_apply _ _ (v i) _ _ (hg i) (hh i), hΔi, (hg i x).fderiv]
  simp [Complex.real_smul]

end Principal

variable {d : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (hd : 2 ≤ d) [Nontrivial (ℝ^n)]

/-- The constructed full spatial semigroup has the paper's differential generator
on twice BUC differentiable diffusion-coordinate data. -/
theorem exists_frontSpatial_generator_eq_pde
    (v : Fin n → BUC (ℝ^d) ℂ) (g : Fin n → BUC (ℝ^d) (ℝ^d →L[ℝ] ℂ))
    (h : Fin n → BUC (ℝ^d) (ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℂ))
    (hg : ∀ i x, HasFDerivAt (v i) (g i x) x) (hh : ∀ i x, HasFDerivAt (g i) (h i x) x) :
    ∃ w : BUC (ℝ^d) (ℂ^n),
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).HasGeneratorAt
        (spatialDiffusionBUCCoordinatesEquiv D h₁.positive v) w ∧
      ∀ x, w x =
        frontComplexifiedDiffusion D (Δ (spatialDiffusionBUCCoordinatesEquiv D h₁.positive v : ℝ^d → ℂ^n) x) +
          fderiv ℝ (spatialDiffusionBUCCoordinatesEquiv D h₁.positive v) x (frontSpatialDrift hd c) +
          (ContinuousLinearMap.complexify (fderiv ℝ f (φ (horizontal x)))) (spatialDiffusionBUCCoordinatesEquiv D h₁.positive v x) := by
  refine ⟨_, frontSpatialC0Semigroup_hasGeneratorAt f D c φ h₁ h₂ hd v g h hg hh, ?_⟩
  intro x
  rw [BUC.add_apply, spatialDiffusionGenerator_coordinates D h₁.positive _ v g h hg hh,
    frontSpatialReactionMultiplication_apply]

/-- The data on which the spatial generator has the classical differential
expression are dense in BUC. This is density in the supremum norm; it does not
assert the stronger graph-norm core property. -/
theorem dense_frontSpatial_classicalGenerator :
    Dense {v : BUC (ℝ^d) (ℂ^n) | ∃ w : BUC (ℝ^d) (ℂ^n),
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).HasGeneratorAt v w ∧
      ∀ x, w x = frontComplexifiedDiffusion D (Δ (v : ℝ^d → ℂ^n) x) +
        fderiv ℝ v x (frontSpatialDrift hd c) +
        (ContinuousLinearMap.complexify (fderiv ℝ f (φ (horizontal x)))) (v x)} := by
  intro v
  let J := spatialDiffusionBUCCoordinatesEquiv (E := ℝ^d) D h₁.positive
  let u : ℝ → BUC (ℝ^d) (ℂ^n) := fun t ↦ J (fun i ↦ heatFlowBUC 1 t (J.symm v i))
  have hc : Continuous u := J.continuous.comp
    (continuous_pi fun i ↦ continuous_heatFlowBUC_time 1 (J.symm v i))
  have hzero : u 0 = v := by simp [u]
  have hlim : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    rw [← hzero]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply subset_closure
  choose g h hg hh using fun i : Fin n ↦
    exists_buc_fderivatives_heatFlow zero_lt_one ht (J.symm v i)
  exact exists_frontSpatial_generator_eq_pde f D c φ h₁ h₂ hd
    (fun i ↦ heatFlowBUC 1 t (J.symm v i)) g h hg hh

end

end Planarwave
