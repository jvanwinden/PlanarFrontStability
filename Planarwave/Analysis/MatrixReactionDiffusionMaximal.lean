/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.MatrixReactionDiffusionLocalClassical
import Planarwave.Analysis.FiniteHeatSystemMaximal

/-!
# Maximal classical reaction--diffusion solutions

This constructs the maximal solution used at the start of the paper's
final proof. The lifetime is positive and possibly infinite; all compact
restrictions are mild solutions, and therefore classical and jointly
smooth at positive times. At a finite endpoint the norm limsup is infinite.
-/

open Set Filter
open scoped ContDiff InnerProductSpace Laplacian Topology ENNReal

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Nontrivial (ℝ^n)]

/-- A maximal continuous mild trajectory, with the original matrix data
and the finite-endpoint blow-up alternative. Joint classical regularity
is derived below, rather than assumed as solution data. -/
structure IsMaximalMatrixReactionDiffusion
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    (u₀ : BUC E (ℝ^n)) (T : ℝ≥0∞) (u : ℝ → BUC E (ℝ^n)) : Prop where
  positive : 0 < T
  initial : u 0 = u₀
  continuous : ContinuousOn u {t | 0 ≤ t ∧ ENNReal.ofReal t < T}
  mild : ∀ S : ℝ, 0 ≤ S → ENNReal.ofReal S < T →
    IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive S u
  maximal : ∀ (S : ℝ) (v : ℝ → BUC E (ℝ^n)), 0 ≤ S → ContinuousOn v (Icc 0 S) →
    v 0 = u₀ → IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive S v →
    ENNReal.ofReal S < T ∧ EqOn u v (Icc 0 S)
  blowup : ∀ R : ℝ, 0 < R → T = ENNReal.ofReal R →
    Filter.limsup (fun t ↦ (‖u t‖₊ : ℝ≥0∞)) (𝓝[<] R) = (⊤ : ℝ≥0∞)

/-- Every BUC initial datum has a maximal solution, under exactly the
original smooth parabolic assumptions. -/
theorem exists_maximal_matrixReactionDiffusion
    (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (h₁ : IsSmoothParabolic f D)
    (u₀ : BUC E (ℝ^n)) :
    ∃ T u, IsMaximalMatrixReactionDiffusion f D h₁ u₀ T u := by
  let b := h₁.positive.toLinearMap.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let P := matrixDiffusionCoordinate D h₁.positive
  let Q (i : Fin n) := ContinuousLinearMap.toSpanSingleton ℝ (b i)
  have hPQ (z : ℝ^n) : ∑ i, Q i (P i z) = z := b.sum_repr' z
  have hQP (i j : Fin n) (z : ℝ) : P i (Q j z) = if i = j then z else 0 := by
    change ⟪b i, z • b j⟫_ℝ = _
    rw [real_inner_smul_right, b.inner_eq_ite]
    split_ifs <;> simp
  obtain ⟨T, hT, u, hinit, hu, hm, hmax, hblow⟩ := exists_maximal_finiteHeatSystem
    (diffusionEigenvalues D h₁.positive) (diffusionEigenvalues_nonneg D h₁.positive)
    P Q hPQ hQP f h₁.smooth u₀
  exact ⟨T, u, hT, hinit, hu, hm, hmax, hblow⟩

namespace IsMaximalMatrixReactionDiffusion

variable {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} {h₁ : IsSmoothParabolic f D}
  {u₀ : BUC E (ℝ^n)} {T : ℝ≥0∞} {u : ℝ → BUC E (ℝ^n)}
  (hm : IsMaximalMatrixReactionDiffusion f D h₁ u₀ T u)

include hm

omit [Nontrivial (ℝ^n)] in
/-- Norm continuity on each compact subinterval of the maximal lifetime. -/
theorem continuousOn_Icc {S : ℝ} (hS : ENNReal.ofReal S < T) :
    ContinuousOn u (Icc 0 S) := hm.continuous.mono (fun _ ht ↦
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hS⟩)

omit [Nontrivial (ℝ^n)] in
/-- The exact challenge continuity condition on every finite slab below
the maximal lifetime. -/
theorem isBUCOn {S : ℝ} (hS : ENNReal.ofReal S < T) :
    IsBUCOn (fun p : ℝ × E ↦ u p.1 p.2) (Icc 0 S ×ˢ univ) :=
  isBUCOn_buc_trajectory_slab (hm.continuousOn_Icc hS)

/-- The maximal trajectory is jointly smooth on its positive-time domain. -/
theorem contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ u p.1 p.2)
      ({t | 0 < t ∧ ENNReal.ofReal t < T} ×ˢ univ) := by
  intro p hp
  obtain ⟨S, hS, hpS, hST⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp.1.2
  have hlt : p.1 < S := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp.1.1.le).mp hpS
  have hc := (hm.mild S hS hST).contDiffOn_infty_of_continuousOn h₁ hS (hm.continuousOn_Icc hST)
  exact (hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
    ⟨⟨hp.1.1, hlt⟩, mem_univ _⟩)).contDiffWithinAt

/-- The maximal trajectory satisfies the actual pointwise PDE at every
positive time before its lifetime. -/
theorem hasDerivAt {t : ℝ} (ht : 0 < t) (htT : ENNReal.ofReal t < T) (x : E) :
    HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → ℝ^n) x) + f (u t x)) t := by
  obtain ⟨S, hS, htS, hST⟩ := ENNReal.lt_iff_exists_real_btwn.mp htT
  have hlt : t < S := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp htS
  exact (hm.mild S hS hST).hasDerivAt_of_continuousOn h₁ hS (hm.continuousOn_Icc hST) ⟨ht, hlt⟩ x

end IsMaximalMatrixReactionDiffusion

end

end Planarwave
