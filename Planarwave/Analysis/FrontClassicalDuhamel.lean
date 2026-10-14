/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontSpatialGenerator
import Planarwave.Analysis.BUCLinearPullback
import Planarwave.Analysis.SemigroupVariationOfConstants
import Planarwave.Analysis.BUCPointwiseTimeDerivative

/-!
# Classical perturbations and the front's Duhamel response

Time-continuous spatial BUC jets give the generator of the actual full
linearized front semigroup. This connects positive-time classical equations
to the semigroup response used in the paper's tracking estimate, without
requiring spatial derivatives of the initial perturbation.
-/

open Set
open scoped Laplacian

namespace Planarwave

noncomputable section

set_option maxHeartbeats 1200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (hd : 2 ≤ d) [Nontrivial (ℝ^n)]

local instance : NormedAddCommGroup (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance : NormedSpace ℂ (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance : NormedSpace ℝ (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance : NormedAddCommGroup (BUC (ℝ^d) ℂ) := inferInstance
local instance : NormedSpace ℝ (BUC (ℝ^d) ℂ) := inferInstance

/-- Two time-continuous spatial BUC derivatives construct a continuous
generator path, with exactly the differential expression in the paper.
Generator membership is a conclusion, not an additional hypothesis. -/
theorem exists_continuous_frontSpatial_generator
    {s : Set ℝ} {u : ℝ → BUC (ℝ^d) (ℂ^n)}
    (hreg : BUCSpatialRegularOn s 2 u) :
    ∃ a : ℝ → BUC (ℝ^d) (ℂ^n), ContinuousOn a s ∧
      (∀ t ∈ s, (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).HasGeneratorAt (u t) (a t)) ∧
      ∀ t ∈ s, ∀ x, a t x =
        frontComplexifiedDiffusion D (Δ (u t : ℝ^d → ℂ^n) x) +
          fderiv ℝ (u t) x (frontSpatialDrift hd c) +
          (fderiv ℝ f (φ (horizontal x))).complexify (u t x) := by
  let J := spatialDiffusionBUCCoordinatesEquiv (E := ℝ^d) D h₁.positive
  let P (i : Fin n) : ℂ^n →L[ℝ] ℂ :=
    ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (diffusionCoordinatesEquiv D h₁.positive).symm.toContinuousLinearMap).restrictScalars ℝ
  have hcoord (i : Fin n) :
      BUCSpatialRegularOn s 2 (fun t ↦ J.symm (u t) i) := by
    apply (hreg.postcompCLM (P i)).congr
    intro t _
    ext x
    rfl
  choose q hq hqderiv using fun i : Fin n ↦ (hcoord i).2
  choose H hH hHderiv using fun i : Fin n ↦ (hq i).2
  let a : ℝ → BUC (ℝ^d) (ℂ^n) := fun t ↦
    J (fun i ↦ convectiveGeneratorBUC (diffusionEigenvalues D h₁.positive i)
      (frontSpatialDrift hd c) (q i t) (H i t)) +
      frontSpatialReactionMultiplication f D c φ h₁ h₂ hd (u t)
  have ha : ContinuousOn a s := by
    apply ContinuousOn.add
    · apply J.continuous.comp_continuousOn
      apply continuousOn_pi.mpr
      intro i
      simpa only [convectiveGeneratorBUC] using!
        (((BUC.postcompCLM (laplacianTraceCLM (E := ℝ^d) (F := ℂ))).continuous.comp_continuousOn
        (hH i).continuous).const_smul (diffusionEigenvalues D h₁.positive i)).add
        ((BUC.postcompCLM (ContinuousLinearMap.apply ℝ ℂ (frontSpatialDrift hd c))).continuous.comp_continuousOn
          (hq i).continuous)
    · exact (frontSpatialReactionMultiplication f D c φ h₁ h₂ hd).continuous.comp_continuousOn
        hreg.continuous
  refine ⟨a, ha, ?_, ?_⟩
  · intro t ht
    have hg := frontSpatialC0Semigroup_hasGeneratorAt f D c φ h₁ h₂ hd
      (fun i ↦ J.symm (u t) i) (fun i ↦ q i t) (fun i ↦ H i t)
      (fun i x ↦ hqderiv i t ht x) (fun i x ↦ hHderiv i t ht x)
    simpa only [a, J, ContinuousLinearEquiv.apply_symm_apply] using! hg
  · intro t ht x
    have hp := spatialDiffusionGenerator_coordinates D h₁.positive (frontSpatialDrift hd c)
      (fun i ↦ J.symm (u t) i) (fun i ↦ q i t) (fun i ↦ H i t)
      (fun i x ↦ hqderiv i t ht x) (fun i x ↦ hHderiv i t ht x) x
    change J _ x = _ at hp
    simp only [J, ContinuousLinearEquiv.apply_symm_apply] at hp
    change J _ x + frontSpatialReactionMultiplication f D c φ h₁ h₂ hd (u t) x = _
    rw [hp, frontSpatialReactionMultiplication_apply]

/-- The actual classical front equation implies the full spatial Duhamel
formula used by the tracking estimates. Spatial jets are needed only at
positive interior times; the datum at zero is merely BUC. This does not
assume that the given path is the inverse modulation of an RDE solution. -/
theorem frontSpatial_eq_realOrbit_add_duhamel_of_classical
    {T : ℝ} {u F : ℝ → BUC (ℝ^d) (ℂ^n)}
    (hu : ContinuousOn u (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T))
    (hreg : BUCSpatialRegularOn (Ioo 0 T) 2 u)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r ↦ u r x)
      (frontComplexifiedDiffusion D (Δ (u t : ℝ^d → ℂ^n) x) +
        fderiv ℝ (u t) x (frontSpatialDrift hd c) +
        (fderiv ℝ f (φ (horizontal x))).complexify (u t x) + F t x) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    u t = (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit (u 0) t +
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel F t := by
  obtain ⟨a, ha, hgen, hformula⟩ :=
    exists_continuous_frontSpatial_generator f D c φ h₁ h₂ hd hreg
  have htime : ∀ r ∈ Ioo 0 T, HasDerivAt u (a r + F r) r := by
    intro r hr
    apply BUC.hasDerivAt_of_pointwise_on_Ioo
      (hu.mono Ioo_subset_Icc_self) (ha.add (hF.mono Ioo_subset_Icc_self))
      (t := r) (ht := hr)
    intro s hs x
    simpa only [Pi.add_apply, BUC.add_apply, hformula s hs x] using! hpde s hs x
  exact (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).eq_realOrbit_add_duhamel_of_hasDerivAt
    hu hF hgen htime ht

end

end Planarwave
