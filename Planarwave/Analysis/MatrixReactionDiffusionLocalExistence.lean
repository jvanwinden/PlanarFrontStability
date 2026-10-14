/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionRegularity
import Planarwave.Analysis.FiniteHeatSystemLocalExistence
import Planarwave.Analysis.FiniteHeatSystemClassical

/-!
# Local solutions of the original matrix reaction--diffusion equation

The real orthonormal diffusion eigenbasis satisfies the coordinate
reconstruction identities. Thus the nonlinear heat-system contraction
applies to the original reaction and diffusion under `IsSmoothParabolic`.
The previously proved parabolic estimates apply to these constructed
solutions, without any assumed spatial regularity of the initial datum.

Positive-time spatial smoothing also gives a genuine time derivative
satisfying the original PDE. Joint spacetime smoothness and continuation
remain separate obligations.
-/

open Set
open scoped ContDiff InnerProductSpace Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- Local mild existence for the original diffusion and reaction. Both
the lifetime and the solution bound precede the choice of initial datum. -/
theorem exists_local_matrixReactionDiffusion
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ T > 0, T ≤ 1 ∧ ∃ R > 0, ∀ u₀ : BUC E (ℝ^n), ‖u₀‖ ≤ B →
      ∃ u : ℝ → BUC E (ℝ^n), Continuous u ∧ u 0 = u₀ ∧ (∀ t, ‖u t‖ ≤ R) ∧
        IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u := by
  let b := h₁.positive.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let P := matrixDiffusionCoordinate D h₁.positive
  let Q (i : Fin n) := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hPQ (v : ℝ^n) : ∑ i, Q i (P i v) = v := b.sum_repr' v
  have hQP (i j : Fin n) (z : ℝ) : P i (Q j z) = if i = j then z else 0 := by
    change ⟪b i, z • b j⟫_ℝ = _
    rw [real_inner_smul_right, b.inner_eq_ite]
    split_ifs <;> simp
  obtain ⟨T, hT, hT₁, hex⟩ := exists_local_finiteHeatSystem (E := E)
    (diffusionEigenvalues D h₁.positive) (diffusionEigenvalues_nonneg D h₁.positive)
    P Q hPQ hQP f h₁.smooth hB
  refine ⟨T, hT, hT₁, (∑ i, ‖Q i‖ * ‖P i‖) * B + 1, ?_, hex⟩
  have : 0 ≤ ∑ i, ‖Q i‖ * ‖P i‖ := Finset.sum_nonneg fun i _ ↦ by positivity
  positivity

/-- The constructed mild solutions have every finite order of spatial
BUC regularity at positive times. This discharges the smoothing input
for local solutions starting from arbitrary bounded uniformly continuous
data, not merely from smooth initial perturbations. -/
theorem exists_local_matrixReactionDiffusion_regular
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ T > 0, T ≤ 1 ∧ ∃ R > 0, ∀ u₀ : BUC E (ℝ^n), ‖u₀‖ ≤ B →
      ∃ u : ℝ → BUC E (ℝ^n), Continuous u ∧ u 0 = u₀ ∧ (∀ t, ‖u t‖ ≤ R) ∧
        IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u ∧
        ∀ (k : ℕ) (δ : ℝ), 0 < δ → BUCSpatialRegularOn (Icc δ T) k u ∧
          ∃ C > 0, ∀ t ∈ Icc δ T, BUCSpatialBound k (u t) C := by
  obtain ⟨T, hT, hT₁, R, hR, hex⟩ := exists_local_matrixReactionDiffusion (E := E) f D h₁ hB
  refine ⟨T, hT, hT₁, R, hR, fun u₀ hu₀ ↦ ?_⟩
  obtain ⟨u, hu, hinit, hb, hm⟩ := hex u₀ hu₀
  refine ⟨u, hu, hinit, hb, hm, fun k δ hδ ↦ ?_⟩
  obtain ⟨C, hC, hCb⟩ := exists_matrixReactionDiffusion_cn_bound (E := E) f D h₁ k hδ hR.le
  have hs := hCb T hT.le u hu.continuousOn (fun t _ ↦ hb t) hm
  exact ⟨hs.1, C, hC, hs.2⟩

/-- Every bounded matrix mild solution satisfies the original PDE at
positive interior times. The time derivative is proved from the restart
equations and automatic spatial smoothing. -/
theorem IsMatrixReactionDiffusionMildOn.hasDerivAt
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} (h₁ : IsSmoothParabolic f D)
    {T B : ℝ} {u : ℝ → BUC E (ℝ^n)}
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ r ∈ Icc 0 T, ‖u r‖ ≤ B)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : E) :
    HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → ℝ^n) x) + f (u t x)) t := by
  have hhalf : 0 < t / 2 := div_pos ht.1 (by norm_num)
  obtain ⟨C, hC, hCb⟩ := exists_matrixReactionDiffusion_cn_bound (E := E) f D h₁ 2 hhalf hB
  have hreg := (hCb T (ht.1.trans ht.2).le u hu.continuousOn hb hm).1
  let b := h₁.positive.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let Q (i : Fin n) := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hPQ (v : ℝ^n) : ∑ i, Q i (matrixDiffusionCoordinate D h₁.positive i v) = v :=
    b.sum_repr' v
  obtain ⟨μ, hμ, hμa⟩ := exists_pos_le_diffusionEigenvalues D h₁.positive h₁.kernel
  exact IsFiniteHeatSystemMildOn.hasDerivAt (fun i ↦ hμ.trans_le (hμa i)) Q hPQ D
    (matrixDiffusionCoordinate_apply_diffusion D h₁.positive) h₁.smooth hm hu hhalf.le hreg
    ⟨by linarith, ht.2⟩ x

/-- Local solutions with smooth spatial slices and a classical time
derivative satisfying the original reaction--diffusion PDE. The stronger
joint spacetime `ContDiffOn` required by `IsRDESolution` is not asserted here. -/
theorem exists_local_matrixReactionDiffusion_pde
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ T > 0, T ≤ 1 ∧ ∃ R > 0, ∀ u₀ : BUC E (ℝ^n), ‖u₀‖ ≤ B →
      ∃ u : ℝ → BUC E (ℝ^n), Continuous u ∧ u 0 = u₀ ∧ (∀ t, ‖u t‖ ≤ R) ∧
        IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u ∧
        ∀ t ∈ Ioo 0 T, ContDiff ℝ ∞ (u t : E → ℝ^n) ∧
          ∀ x, HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → ℝ^n) x) + f (u t x)) t := by
  obtain ⟨T, hT, hT₁, R, hR, hex⟩ :=
    exists_local_matrixReactionDiffusion_regular (E := E) f D h₁ hB
  refine ⟨T, hT, hT₁, R, hR, fun u₀ hu₀ ↦ ?_⟩
  obtain ⟨u, hu, hinit, hb, hm, hreg⟩ := hex u₀ hu₀
  refine ⟨u, hu, hinit, hb, hm, fun t ht ↦ ⟨?_, ?_⟩⟩
  · apply contDiff_infty.mpr
    intro k
    exact (hreg k (t / 2) (div_pos ht.1 (by norm_num))).1.contDiff
      ⟨by linarith [ht.1], ht.2.le⟩
  · exact fun x ↦ hm.hasDerivAt h₁ hu hR.le (fun r _ ↦ hb r) ht x

end

end Planarwave
