/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.SpatialDiffusionSmoothing
import Planarwave.Analysis.SemigroupTaylor
import Planarwave.Analysis.SemigroupHolomorphic
import Planarwave.Analysis.SemigroupSector
import Planarwave.Analysis.SemigroupAnalyticPerturbation
import Planarwave.Analysis.SemigroupAnalyticSmoothing

/-!
# Analytic generation on the full spatial BUC space

The quantitative Gaussian smoothing estimate gives a holomorphic time extension
of the actual full spatial matrix diffusion semigroup. The bounded reaction
coefficient preserves analytic generation, as in the paper's parabolic argument.
This concerns the independently constructed spatial evolution, not merely its
longitudinal Fourier symbols.
-/

open Filter Set Topology
open scoped ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

section Principal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- Uniformly bounded local complex-time evolution, with the genuine initial limit. -/
theorem exists_spatialDiffusion_bounded_holomorphic_timeExtension
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (b : E) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ N > 0,
      ∃ g : ℂ → (BUC E (ℂ^n) →L[ℂ] BUC E (ℂ^n)),
        AnalyticOnNhd ℂ g (positiveTimeNeighborhood η) ∧
        (∀ t : ℝ, 0 < t → g t = spatialDiffusionC0Semigroup D hD b t.toNNReal) ∧
        (∀ z ∈ positiveTimeNeighborhood η, ‖g z‖ ≤ N) ∧
        (∀ v, Tendsto (fun z ↦ g z v) (𝓝[positiveTimeNeighborhood η] 0) (𝓝 v)) := by
  obtain ⟨C, hC, hsmooth⟩ := exists_spatialDiffusion_generator_opNorm_bound D hD hDinj b
  obtain ⟨M, hM, hbound⟩ := exists_uniform_spatialDiffusion_bound (E := E) D hD
  let S : Unit → C0Semigroup ℂ (BUC E (ℂ^n)) := fun _ ↦ spatialDiffusionC0Semigroup D hD b
  obtain ⟨η, hη, hηhalf, L, hL, hext⟩ :=
    C0Semigroup.exists_uniform_bounded_analytic_extension_of_smoothing S hC.le
      (fun _ r hr hr₁ ↦ hsmooth r hr hr₁)
  have hη₁ : η ≤ 1 := hηhalf.trans (by norm_num)
  obtain ⟨g, hg, heq, hgb⟩ := exists_bounded_analytic_extension_positiveTimeNeighborhood
    hη hη₁ (fun t ht ↦ hext t ht () M hM.le (fun s _ ↦ hbound b s))
  exact ⟨η, hη, hηhalf, L * M, mul_pos hL hM, g, hg, heq, hgb,
    fun v ↦ (S ()).tendsto_holomorphicExtension_zero
      hη hη₁ (mul_pos hL hM).le hg heq hgb v⟩

/-- Analytic generation for full spatial matrix diffusion and drift. The complex
semigroup obeys the semigroup law and converges strongly to the identity at zero. -/
theorem exists_spatialDiffusion_holomorphic_sector
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (b : E) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ M > 0, ∃ κ > 0,
      ∃ G : ℂ → (BUC E (ℂ^n) →L[ℂ] BUC E (ℂ^n)),
        AnalyticOnNhd ℂ G (complexTimeSector η) ∧
        (∀ t : ℝ, 0 < t → G t = spatialDiffusionC0Semigroup D hD b t.toNNReal) ∧
        (∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
          G (z + w) = (G z).comp (G w)) ∧
        (∀ v, Tendsto (fun z ↦ G z v) (𝓝[complexTimeSector η] 0) (𝓝 v)) ∧
        (∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (κ * z.re)) := by
  obtain ⟨η, hη, hηhalf, N, hN, g, hg, hreal, hb, hzero⟩ :=
    exists_spatialDiffusion_bounded_holomorphic_timeExtension D hD hDinj b
  let S := spatialDiffusionC0Semigroup D hD b
  obtain ⟨G, hG, hGreal, heq, hdivide⟩ := S.exists_holomorphic_sector_extension hη hg hreal
  exact ⟨η, hη, hηhalf, Real.exp N, Real.exp_pos N, N, hN, G, hG, hGreal,
    fun _ hz _ hw ↦ S.holomorphicSectorExtension_add hη hG hGreal hz hw,
    fun v ↦ C0Semigroup.tendsto_holomorphicSectorExtension_zero heq hzero v,
    fun _ hz ↦ C0Semigroup.norm_holomorphicSectorExtension_le hN.le hb hdivide hz⟩

end Principal

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (hd : 2 ≤ d) [Nontrivial (ℝ^n)]

/-- The actual spatial linearized evolution is analytic: adding the bounded
reaction coefficient preserves the principal diffusion's holomorphic time sector. -/
theorem exists_frontSpatial_holomorphic_sector :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ M > 0, ∃ κ > 0,
      ∃ G : ℂ → (BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n)),
        AnalyticOnNhd ℂ G (complexTimeSector η) ∧
        (∀ t : ℝ, 0 < t → G t = frontSpatialC0Semigroup f D c φ h₁ h₂ hd t.toNNReal) ∧
        (∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
          G (z + w) = (G z).comp (G w)) ∧
        (∀ v, Tendsto (fun z ↦ G z v) (𝓝[complexTimeSector η] 0) (𝓝 v)) ∧
        (∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (κ * ‖z‖)) := by
  obtain ⟨η, hη, hηhalf, M, hM, κ, hκ, G, hGa, hreal, _, hzero, hb⟩ :=
    exists_spatialDiffusion_holomorphic_sector D h₁.positive h₁.kernel (frontSpatialDrift hd c)
  let B := frontSpatialReactionMultiplication f D c φ h₁ h₂ hd
  refine ⟨η, hη, hηhalf, M, hM, κ + M * ‖B‖, by positivity, ?_⟩
  have hbound : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (κ * ‖z‖) := by
    intro z hz
    exact (hb z hz).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hκ.le)) hM.le)
  exact (spatialDiffusionC0Semigroup D h₁.positive (frontSpatialDrift hd c)).exists_boundedPerturbation_holomorphic_sector
    B hη hM.le hκ.le hGa hbound hreal hzero

/-- Operator-norm real analyticity of the full spatial front evolution at positive times. -/
theorem analyticOnNhd_frontSpatialC0Semigroup :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ frontSpatialC0Semigroup f D c φ h₁ h₂ hd t.toNNReal) (Ioi 0) := by
  obtain ⟨η, hη, _, _, _, _, _, G, hG, hreal, _⟩ :=
    exists_frontSpatial_holomorphic_sector f D c φ h₁ h₂ hd
  intro t ht
  have hgc := hG (t : ℂ) (mem_complexTimeSector_real hη ht)
  have hgr : AnalyticAt ℝ (fun s : ℝ ↦ G (s : ℂ)) t :=
    (hgc.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  apply hgr.congr
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact hreal s hs

/-- In particular the full spatial front evolution is smooth in operator norm. -/
theorem contDiffOn_frontSpatialC0Semigroup :
    ContDiffOn ℝ ∞ (fun t : ℝ ↦ frontSpatialC0Semigroup f D c φ h₁ h₂ hd t.toNNReal) (Ioi 0) :=
  (analyticOnNhd_frontSpatialC0Semigroup f D c φ h₁ h₂ hd).contDiffOn isOpen_Ioi.uniqueDiffOn

/-- Every positive-time spatial orbit belongs to the full generator domain. -/
theorem frontSpatialC0Semigroup_hasGeneratorAt_deriv {t : ℝ} (ht : 0 < t)
    (v : BUC (ℝ^d) (ℂ^n)) :
    (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).HasGeneratorAt
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t.toNNReal v)
      (deriv (fun s : ℝ ↦ frontSpatialC0Semigroup f D c φ h₁ h₂ hd s.toNNReal) t v) := by
  have hdiff := (analyticOnNhd_frontSpatialC0Semigroup f D c φ h₁ h₂ hd t ht).differentiableAt
  exact (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).hasGeneratorAt_of_hasDerivAt_operator
    ht.le hdiff.hasDerivAt v

/-- The full spatial linearized generator, including the reaction coefficient,
has the quantitative short-time parabolic smoothing bound. -/
theorem exists_frontSpatial_generator_opNorm_bound :
    ∃ C > 0, ∀ t : NNReal, 0 < t → t ≤ 1 →
      ∃ B : BUC (ℝ^d) (ℂ^n) →L[ℂ] BUC (ℝ^d) (ℂ^n),
        (∀ v, (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).HasGeneratorAt
          (frontSpatialC0Semigroup f D c φ h₁ h₂ hd t v) (B v)) ∧ ‖B‖ ≤ C / (t : ℝ) := by
  obtain ⟨η, hη, hηhalf, M, hM, κ, hκ, G, hG, hreal, _, _, hb⟩ :=
    exists_frontSpatial_holomorphic_sector f D c φ h₁ h₂ hd
  exact (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).exists_generator_opNorm_bound_of_holomorphic_sector
    hη (hηhalf.trans (by norm_num)) hM hκ.le hG hreal hb

/-- Cauchy's estimate for the actual full spatial operator-valued time derivative. -/
theorem exists_deriv_frontSpatialC0Semigroup_bound :
    ∃ C > 0, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖deriv (fun s : ℝ ↦ frontSpatialC0Semigroup f D c φ h₁ h₂ hd s.toNNReal) t‖ ≤ C / t := by
  obtain ⟨C, hC, hb⟩ := exists_frontSpatial_generator_opNorm_bound f D c φ h₁ h₂ hd
  refine ⟨C, hC, fun t ht ht₁ ↦ ?_⟩
  obtain ⟨B, hB, hnorm⟩ := hb ⟨t, ht.le⟩ ht ht₁
  have heq : deriv (fun s : ℝ ↦ frontSpatialC0Semigroup f D c φ h₁ h₂ hd s.toNNReal) t = B := by
    apply ContinuousLinearMap.ext
    intro v
    have hgen := frontSpatialC0Semigroup_hasGeneratorAt_deriv f D c φ h₁ h₂ hd ht v
    rw [Real.toNNReal_of_nonneg ht.le] at hgen
    exact hgen.unique (hB v)
  rw [heq]
  exact hnorm

end

end Planarwave
