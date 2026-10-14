/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionEigenbasis
import Planarwave.Analysis.FiniteHeatSystemRegularity

/-!
# Higher parabolic bounds for the original diffusion eigenbasis

Instantiate the coupled heat-system bootstrap with the orthonormal
eigenbasis of the challenge's positive injective diffusion. The reaction
is the original vector reaction, not independent scalar reactions.
The remaining solution-construction obligation is to establish these
mild equations for the original reaction--diffusion solution.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- The real scalar coordinate in the same orthonormal eigenbasis used
for the diffusion semigroup in Section 2. -/
def matrixDiffusionCoordinate (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (i : Fin n) :
    ℝ^n →L[ℝ] ℝ :=
  innerSL ℝ (hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i)

omit [Nontrivial (ℝ^n)] in
/-- The coordinate sees exactly the corresponding scalar diffusion rate. -/
theorem matrixDiffusionCoordinate_apply_diffusion (D : ℝ^n →L[ℝ] ℝ^n)
    (hD : D.IsPositive) (i : Fin n) (v : ℝ^n) :
    matrixDiffusionCoordinate D hD i (D v) =
      diffusionEigenvalues D hD i * matrixDiffusionCoordinate D hD i v := by
  change ⟪hD.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin i, D v⟫_ℝ = _
  rw [← hD.inner_left_eq_inner_right]
  have heig := hD.toLinearMap.isSymmetric.apply_eigenvectorBasis finrank_euclideanSpace_fin i
  change D _ = diffusionEigenvalues D hD i • _ at heig
  rw [heig, real_inner_smul_left]
  rfl

/-- The original vector reaction--diffusion mild equations, expressed in
the fixed real diffusion eigenbasis. -/
def IsMatrixReactionDiffusionMildOn (f : ℝ^n → ℝ^n) (hf : Continuous f)
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (T : ℝ) (u : ℝ → BUC E (ℝ^n)) : Prop :=
  IsFiniteHeatSystemMildOn (diffusionEigenvalues D hD) (matrixDiffusionCoordinate D hD)
    f hf T u

/-- It is enough to establish the usual coordinate mild formula from the
initial datum; all later restart formulas follow from the heat semigroup. -/
theorem isMatrixReactionDiffusionMildOn_of_mild
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    {T : ℝ} {u : ℝ → BUC E (ℝ^n)} (hu : ContinuousOn u (Icc 0 T))
    (hm : ∀ t ∈ Icc 0 T, ∀ i,
      BUC.postcompCLM (matrixDiffusionCoordinate D h₁.positive i) (u t) =
        heatFlowBUC (diffusionEigenvalues D h₁.positive i) t
          (BUC.postcompCLM (matrixDiffusionCoordinate D h₁.positive i) (u 0)) +
        heatDuhamel (diffusionEigenvalues D h₁.positive i) (fun r ↦
          BUC.postcompContinuous (fun v ↦ matrixDiffusionCoordinate D h₁.positive i (f v))
            ((matrixDiffusionCoordinate D h₁.positive i).continuous.comp h₁.smooth.continuous)
            (u r)) t) :
    IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u :=
  isFiniteHeatSystemMildOn_of_mild (diffusionEigenvalues D h₁.positive)
    (diffusionEigenvalues_nonneg D h₁.positive) (matrixDiffusionCoordinate D h₁.positive)
    f h₁.smooth hu hm

/-- Uniform all-order parabolic bounds for a bounded solution of the
original matrix mild equations. All constants precede the horizon and
solution, and no spatial derivative of the solution is assumed. -/
theorem exists_matrixReactionDiffusion_cn_bound
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    (k : ℕ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ T : ℝ, 0 ≤ T → ∀ u : ℝ → BUC E (ℝ^n),
      ContinuousOn u (Icc 0 T) → (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u →
      BUCSpatialRegularOn (Icc δ T) k u ∧
        ∀ t ∈ Icc δ T, BUCSpatialBound k (u t) C := by
  let b := h₁.positive.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let Q (i : Fin n) := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hPQ (v : ℝ^n) : ∑ i, Q i (matrixDiffusionCoordinate D h₁.positive i v) = v :=
    b.sum_repr' v
  obtain ⟨μ, hμ, hμa⟩ := exists_pos_le_diffusionEigenvalues D h₁.positive h₁.kernel
  exact exists_finiteHeatSystem_cn_bound k (diffusionEigenvalues D h₁.positive)
    (fun i ↦ hμ.trans_le (hμa i)) (matrixDiffusionCoordinate D h₁.positive) Q hPQ
    hδ hB f h₁.smooth

/-- The precise cutoff parabolic input of Step 4, for any finite order.
In the paper `k = 9` and the cutoff vanishes below `δ = 1/8`. -/
theorem exists_matrixReactionDiffusion_cutoff_cn_bound
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    (k : ℕ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ T : ℝ, 0 ≤ T → ∀ u : ℝ → BUC E (ℝ^n),
      ContinuousOn u (Icc 0 T) → (∀ t ∈ Icc 0 T, ‖u t‖ ≤ B) →
      IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u →
      ∀ χ : ℝ → ℝ, (∀ t < δ, χ t = 0) → (∀ t, |χ t| ≤ 1) →
      ∀ t ∈ Icc 0 T, BUCSpatialBound k (χ t • u t) C := by
  obtain ⟨C, hC, hb⟩ := exists_matrixReactionDiffusion_cn_bound (E := E) f D h₁ k hδ hB
  refine ⟨C, hC, fun T hT u hu hbound hm χ hχ₀ hχ t ht ↦ ?_⟩
  by_cases hδt : δ ≤ t
  · exact (((hb T hT u hu hbound hm).2 t ⟨hδt, ht.2⟩).smul (χ t)).mono
      (by have := mul_le_mul_of_nonneg_right (hχ t) hC.le; simpa using this)
  · rw [hχ₀ t (lt_of_not_ge hδt)]
    have hzero : (0 : ℝ) • u t = (0 : BUC E (ℝ^n)) := by
      simpa only using! zero_smul ℝ (u t)
    rw [hzero]
    have hz : BUC.const E (0 : ℝ^n) = (0 : BUC E (ℝ^n)) := BUC.ext fun _ ↦ rfl
    simpa only [hz] using
      (BUCSpatialBound.const (E := E) k (0 : ℝ^n)).mono (by simpa using hC.le)

end

end Planarwave
