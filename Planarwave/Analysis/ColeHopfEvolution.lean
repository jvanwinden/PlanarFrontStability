/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ColeHopf
public import Planarwave.Analysis.HeatSemigroup

@[expose] public section

/-!
# Cole--Hopf evolution of bounded uniformly continuous phase data

Construct the candidate viscous Hamilton--Jacobi evolution by applying the inverse Cole--Hopf
transform to the heat evolution of the transformed initial data. Gaussian averaging preserves
the interval between the transformed extrema, so the logarithmic inverse remains well-defined.
The results here concern the evolution and its bounds; identifying its classical PDE additionally
requires positive-time regularity and the heat equation.
-/

open Set Filter MeasureTheory ProbabilityTheory

namespace Planarwave

noncomputable section

section Composition

variable {A : Type*} [UniformSpace A]

/-- Continuous postcomposition on a compact interval preserves bounded uniform continuity. -/
def _root_.BUC.compOnIcc (u : BUC A ℝ) (g : ℝ → ℝ) {l r : ℝ}
    (hg : ContinuousOn g (Icc l r)) (hu : ∀ x, u x ∈ Icc l r) : BUC A ℝ where
  toBCF :=
    { toFun := fun x => g (u x)
      continuous_toFun := by
        rw [← continuousOn_univ]
        exact hg.comp u.continuous.continuousOn (fun x _ => hu x)
      map_bounded' := Metric.isBounded_range_iff.mp
        (((isCompact_Icc.image_of_continuousOn hg).isBounded).subset (by
          rintro _ ⟨x, rfl⟩
          exact ⟨u x, hu x, rfl⟩)) }
  uniformContinuous' := by
    rw [← uniformContinuousOn_univ]
    exact (isCompact_Icc.uniformContinuousOn_of_continuous hg).comp
      u.uniformContinuous.uniformContinuousOn (fun x _ => hu x)

@[simp]
theorem _root_.BUC.compOnIcc_apply (u : BUC A ℝ) (g : ℝ → ℝ) {l r : ℝ}
    (hg : ContinuousOn g (Icc l r)) (hu : ∀ x, u x ∈ Icc l r) (x : A) :
    u.compOnIcc g hg hu x = g (u x) := rfl

/-- The normalized Cole--Hopf transform on BUC data, including the zero-parameter case. -/
def coleHopfBUC (β : ℝ) (u : BUC A ℝ) : BUC A ℝ :=
  u.compOnIcc (coleHopf β) (contDiff_coleHopf β).continuous.continuousOn
    (fun x => abs_le.mp (show |u x| ≤ ‖u‖ from u.norm_apply_le x))

@[simp]
theorem coleHopfBUC_apply (β : ℝ) (u : BUC A ℝ) (x : A) :
    coleHopfBUC β u x = coleHopf β (u x) := rfl

end Composition

section ScalarInverse

/-- The inverse transform preserves order within its natural domain. -/
theorem coleHopfInv_le_iff {β x y : ℝ}
    (hx : x ∈ coleHopfDomain β) (hy : y ∈ coleHopfDomain β) :
    coleHopfInv β x ≤ coleHopfInv β y ↔ x ≤ y := by
  rw [← (strictMono_coleHopf β).le_iff_le,
    coleHopf_coleHopfInv hx, coleHopf_coleHopfInv hy]

/-- The entire interval between transformed extrema lies in the inverse's domain. -/
theorem Icc_coleHopf_subset_domain (β R : ℝ) :
    Icc (coleHopf β (-R)) (coleHopf β R) ⊆ coleHopfDomain β := by
  intro x hx
  rw [mem_coleHopfDomain]
  by_cases hβ : 0 ≤ β
  · exact lt_of_lt_of_le (mem_coleHopfDomain.mp (coleHopf_mem_domain β (-R)))
      (mul_le_mul_of_nonneg_left hx.1 hβ)
  · exact lt_of_lt_of_le (mem_coleHopfDomain.mp (coleHopf_mem_domain β R))
      (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hβ))

/-- Inverting a value between the transformed extrema gives a value between the extrema. -/
theorem coleHopfInv_mem_Icc {β R x : ℝ}
    (hx : x ∈ Icc (coleHopf β (-R)) (coleHopf β R)) :
    coleHopfInv β x ∈ Icc (-R) R := by
  have hdomain := Icc_coleHopf_subset_domain β R hx
  constructor
  · simpa using (coleHopfInv_le_iff (coleHopf_mem_domain β (-R)) hdomain).2 hx.1
  · simpa using (coleHopfInv_le_iff hdomain (coleHopf_mem_domain β R)).2 hx.2

end ScalarInverse

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian averaging preserves pointwise lower and upper bounds. -/
theorem heatFlowBUC_mem_Icc (a t : ℝ) (u : BUC E ℝ) {l r : ℝ}
    (hu : ∀ x, u x ∈ Icc l r) (x : E) : heatFlowBUC a t u x ∈ Icc l r := by
  have hint := integrable_comp_add_heatScale (a := a) (t := t) u.continuous
    ‖u‖ u.norm_apply_le x
  constructor
  · have h := integral_mono (integrable_const l) hint (fun z => (hu _).1)
    simpa [heatFlowBUC_apply, heatFlow] using h
  · have h := integral_mono hint (integrable_const r) (fun z => (hu _).2)
    simpa [heatFlowBUC_apply, heatFlow] using h

/-- The transformed heat orbit stays between the transformed extrema for all times. -/
theorem heatFlowBUC_coleHopf_mem_Icc (a β t : ℝ) (u : BUC E ℝ) (x : E) :
    heatFlowBUC a t (coleHopfBUC β u) x ∈
      Icc (coleHopf β (-‖u‖)) (coleHopf β ‖u‖) := by
  apply heatFlowBUC_mem_Icc
  intro y
  have hy := abs_le.mp (show |u y| ≤ ‖u‖ from u.norm_apply_le y)
  exact ⟨(strictMono_coleHopf β).monotone hy.1,
    (strictMono_coleHopf β).monotone hy.2⟩

/-- Candidate viscous Hamilton--Jacobi evolution in transverse BUC, with `β = c/(2a)` in
the PDE application. -/
def coleHopfEvolution (a β t : ℝ) (u : BUC E ℝ) : BUC E ℝ :=
  (heatFlowBUC a t (coleHopfBUC β u)).compOnIcc (coleHopfInv β)
    ((contDiffOn_coleHopfInv β).continuousOn.mono (Icc_coleHopf_subset_domain β ‖u‖))
    (heatFlowBUC_coleHopf_mem_Icc a β t u)

@[simp]
theorem coleHopfEvolution_apply (a β t : ℝ) (u : BUC E ℝ) (x : E) :
    coleHopfEvolution a β t u x =
      coleHopfInv β (heatFlowBUC a t (coleHopfBUC β u) x) := rfl

/-- The candidate evolution attains its initial datum exactly. -/
@[simp]
theorem coleHopfEvolution_zero (a β : ℝ) (u : BUC E ℝ) :
    coleHopfEvolution a β 0 u = u := by
  ext x
  simp

/-- With zero nonlinear coefficient, the construction is the ordinary heat evolution. -/
@[simp]
theorem coleHopfEvolution_zero_parameter (a t : ℝ) (u : BUC E ℝ) :
    coleHopfEvolution a 0 t u = heatFlowBUC a t u := by
  have hu : coleHopfBUC 0 u = u := by ext x; simp
  ext x
  simp [hu]

/-- The Cole--Hopf evolution preserves the bound on the initial phase. -/
theorem norm_coleHopfEvolution_le (a β t : ℝ) (u : BUC E ℝ) :
    ‖coleHopfEvolution a β t u‖ ≤ ‖u‖ := by
  apply (BUC.norm_le (norm_nonneg u)).2
  intro x
  exact abs_le.mpr (coleHopfInv_mem_Icc (heatFlowBUC_coleHopf_mem_Icc a β t u x))

/-- Transforming the constructed evolution recovers precisely the linear heat orbit. -/
@[simp]
theorem coleHopfBUC_coleHopfEvolution (a β t : ℝ) (u : BUC E ℝ) :
    coleHopfBUC β (coleHopfEvolution a β t u) = heatFlowBUC a t (coleHopfBUC β u) := by
  ext x
  exact coleHopf_coleHopfInv (Icc_coleHopf_subset_domain β ‖u‖
    (heatFlowBUC_coleHopf_mem_Icc a β t u x))

/-- The nonlinear evolution inherits the heat semigroup law through the transform. -/
theorem coleHopfEvolution_add_time {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (β : ℝ) (u : BUC E ℝ) :
    coleHopfEvolution a β s (coleHopfEvolution a β t u) =
      coleHopfEvolution a β (s + t) u := by
  ext x
  simp only [coleHopfEvolution_apply, coleHopfBUC_coleHopfEvolution]
  have h := congrFun (heatFlow_add_time ha hs ht (coleHopfBUC β u).uniformContinuous
    (coleHopfBUC β u).norm_apply_le) x
  exact congrArg (coleHopfInv β) h

/-- Continuity of the candidate evolution in the BUC norm, including the initial time. -/
theorem continuous_coleHopfEvolution_time (a β : ℝ) (u : BUC E ℝ) :
    Continuous (fun t : ℝ => coleHopfEvolution a β t u) := by
  have hinv := isCompact_Icc.uniformContinuousOn_of_continuous
    ((contDiffOn_coleHopfInv β).continuousOn.mono (Icc_coleHopf_subset_domain β ‖u‖))
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hinv (ε / 2) (by positivity)
  obtain ⟨η, hη, htime⟩ := Metric.continuousAt_iff.mp
    (continuous_heatFlowBUC_time a (coleHopfBUC β u)).continuousAt δ hδ
  refine ⟨η, hη, ?_⟩
  intro s hs
  have hst : ‖heatFlowBUC a s (coleHopfBUC β u) -
      heatFlowBUC a t (coleHopfBUC β u)‖ < δ := by
    simpa only [dist_eq_norm] using htime hs
  have hsup : ‖coleHopfEvolution a β s u - coleHopfEvolution a β t u‖ ≤ ε / 2 := by
    apply (BUC.norm_le (by positivity)).2
    intro x
    have hx : dist (heatFlowBUC a s (coleHopfBUC β u) x)
        (heatFlowBUC a t (coleHopfBUC β u) x) < δ := by
      rw [dist_eq_norm]
      exact ((heatFlowBUC a s (coleHopfBUC β u) -
        heatFlowBUC a t (coleHopfBUC β u)).norm_apply_le x).trans_lt hst
    exact (hmod _ (heatFlowBUC_coleHopf_mem_Icc a β s u x)
      _ (heatFlowBUC_coleHopf_mem_Icc a β t u x) hx).le
  rw [dist_eq_norm]
  exact hsup.trans_lt (by linarith)

/-- All time slices share a common spatial modulus of continuity. -/
theorem equiuniformContinuous_coleHopfEvolution (a β : ℝ) (u : BUC E ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, ∀ x y : E, dist x y < δ →
      dist (coleHopfEvolution a β t u x) (coleHopfEvolution a β t u y) < ε := by
  intro ε hε
  have hinv := isCompact_Icc.uniformContinuousOn_of_continuous
    ((contDiffOn_coleHopfInv β).continuousOn.mono (Icc_coleHopf_subset_domain β ‖u‖))
  obtain ⟨η, hη, hinvmod⟩ := Metric.uniformContinuousOn_iff.mp hinv ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp (coleHopfBUC β u).uniformContinuous
    (η / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t x y hxy
  apply hinvmod _ (heatFlowBUC_coleHopf_mem_Icc a β t u x)
    _ (heatFlowBUC_coleHopf_mem_Icc a β t u y)
  rw [dist_eq_norm]
  change ‖(∫ z, coleHopfBUC β u (x + heatScale a t • z) ∂stdGaussian E) -
    ∫ z, coleHopfBUC β u (y + heatScale a t • z) ∂stdGaussian E‖ < η
  rw [← integral_sub
    (integrable_comp_add_heatScale (coleHopfBUC β u).continuous
      ‖coleHopfBUC β u‖ (coleHopfBUC β u).norm_apply_le x)
    (integrable_comp_add_heatScale (coleHopfBUC β u).continuous
      ‖coleHopfBUC β u‖ (coleHopfBUC β u).norm_apply_le y)]
  have hbound : ∀ᵐ z ∂stdGaussian E,
      ‖coleHopfBUC β u (x + heatScale a t • z) -
        coleHopfBUC β u (y + heatScale a t • z)‖ ≤ η / 2 := by
    filter_upwards [] with z
    exact (hmod (by simpa only [dist_add_right] using hxy)).le
  have h := norm_integral_le_of_norm_le_const hbound
  have h' : ‖∫ z, coleHopfBUC β u (x + heatScale a t • z) -
      coleHopfBUC β u (y + heatScale a t • z) ∂stdGaussian E‖ ≤ η / 2 := by
    simpa using h
  exact h'.trans_lt (by linarith)

/-- Uniform continuity on each finite time slab, in precisely the product topology used by the
challenge's solution predicate. -/
theorem uniformContinuousOn_coleHopfEvolution_slab (a β T : ℝ) (u : BUC E ℝ) :
    UniformContinuousOn (fun p : ℝ × E => coleHopfEvolution a β p.1 u p.2)
      (Icc 0 T ×ˢ (univ : Set E)) := by
  have htime : UniformContinuousOn (fun t : ℝ => coleHopfEvolution a β t u) (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
    (continuous_coleHopfEvolution_time a β u).continuousOn
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δt, hδt, hmodt⟩ := Metric.uniformContinuousOn_iff.mp htime (ε / 2) (by positivity)
  obtain ⟨δx, hδx, hmodx⟩ := equiuniformContinuous_coleHopfEvolution a β u (ε / 2)
    (by positivity)
  refine ⟨min δt δx, lt_min hδt hδx, ?_⟩
  intro p hp q hq hpq
  have ht : dist p.1 q.1 < δt := (le_max_left _ _).trans_lt
    (hpq.trans_le (min_le_left _ _))
  have hx : dist p.2 q.2 < δx := (le_max_right _ _).trans_lt
    (hpq.trans_le (min_le_right _ _))
  have htbound : dist (coleHopfEvolution a β p.1 u p.2)
      (coleHopfEvolution a β q.1 u p.2) < ε / 2 := by
    rw [dist_eq_norm]
    exact ((coleHopfEvolution a β p.1 u - coleHopfEvolution a β q.1 u).norm_apply_le p.2).trans_lt
      (by simpa only [dist_eq_norm] using hmodt _ hp.1 _ hq.1 ht)
  calc
    dist (coleHopfEvolution a β p.1 u p.2) (coleHopfEvolution a β q.1 u q.2) ≤
        dist (coleHopfEvolution a β p.1 u p.2) (coleHopfEvolution a β q.1 u p.2) +
        dist (coleHopfEvolution a β q.1 u p.2) (coleHopfEvolution a β q.1 u q.2) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add htbound (hmodx q.1 p.2 q.2 hx)
    _ = ε := by ring

end Evolution

end

end Planarwave
