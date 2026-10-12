/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupPerturbationComposition
public import Planarwave.Analysis.SemigroupPerturbationBound

@[expose] public section

/-!
# Uniform bounds for compact families of bounded perturbations

This is the uniform-semigroup lemma in the paper's appendix. The proof follows its two steps:
the bounded perturbation estimate gives a neighborhood bound around each operator, and a
finite subcover allows the maximum of finitely many prefactors. We retain a common exponential
weight `ω`; setting `ω = 0` gives the appendix statement exactly.
-/

open Set

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The neighborhood estimate used in the appendix, allowing a common initial growth rate. -/
theorem norm_boundedPerturbation_le_of_mem_ball (S : C0Semigroup ℂ E)
    {B C : E →L[ℂ] E} {M ω ε : ℝ} (hM : 0 < M)
    (hbound : ∀ t : NNReal, ‖S.boundedPerturbation B t‖ ≤ M * Real.exp (ω * t))
    (hC : C ∈ Metric.ball B (ε / M)) (t : NNReal) :
    ‖S.boundedPerturbation C t‖ ≤ M * Real.exp ((ω + ε) * t) := by
  have hsmall : M * ‖C - B‖ ≤ ε := by
    have hnorm : ‖C - B‖ < ε / M := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hC
    nlinarith [(lt_div_iff₀ hM).mp hnorm]
  have h := (S.boundedPerturbation B).norm_boundedPerturbation_le
    (C - B) hM.le hbound t
  rw [S.boundedPerturbation_sub] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hsmall) t.2

/-- Pointwise bounds with a common growth rate are uniform on an operator-norm compact family,
at the cost of an arbitrarily small increase in that rate. -/
theorem exists_uniform_boundedPerturbation_bound (S : C0Semigroup ℂ E)
    {K : Set (E →L[ℂ] E)} (hK : IsCompact K) {ω : ℝ}
    (hbound : ∀ B ∈ K, ∃ M > 0, ∀ t : NNReal,
      ‖S.boundedPerturbation B t‖ ≤ M * Real.exp (ω * t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ B ∈ K, ∀ t : NNReal,
      ‖S.boundedPerturbation B t‖ ≤ C * Real.exp ((ω + ε) * t) := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | ⟨B₀, hB₀⟩
  · exact ⟨1, zero_lt_one, by simp [hKe]⟩
  choose M hM hMb using fun B : K ↦ hbound B B.property
  let U : K → Set (E →L[ℂ] E) := fun B ↦ Metric.ball B (ε / M B)
  have hcover : K ⊆ ⋃ B : K, U B := by
    intro B hB
    apply mem_iUnion.mpr
    refine ⟨⟨B, hB⟩, ?_⟩
    exact Metric.mem_ball_self (div_pos hε (hM ⟨B, hB⟩))
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U (fun _ ↦ Metric.isOpen_ball) hcover
  have hFne : F.Nonempty := by
    obtain ⟨B, hBF, _⟩ := mem_iUnion₂.mp (hF hB₀)
    exact ⟨B, hBF⟩
  refine ⟨F.sup' hFne M, ?_, ?_⟩
  · obtain ⟨B, hBF⟩ := hFne
    exact (hM B).trans_le (Finset.le_sup' M hBF)
  · intro B hB t
    obtain ⟨A, hAF, hBA⟩ := mem_iUnion₂.mp (hF hB)
    exact (S.norm_boundedPerturbation_le_of_mem_ball (hM A) (hMb A) hBA t).trans
      (mul_le_mul_of_nonneg_right (Finset.le_sup' M hAF) (Real.exp_pos _).le)

/-- The uniform-semigroup lemma of the appendix: bounded individual semigroups on a compact
perturbation family admit one bound `C exp (ε t)` for every `ε > 0`. -/
theorem exists_uniform_boundedPerturbation_bound_of_bounded (S : C0Semigroup ℂ E)
    {K : Set (E →L[ℂ] E)} (hK : IsCompact K)
    (hbound : ∀ B ∈ K, ∃ M > 0, ∀ t : NNReal, ‖S.boundedPerturbation B t‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ B ∈ K, ∀ t : NNReal,
      ‖S.boundedPerturbation B t‖ ≤ C * Real.exp (ε * t) := by
  have hbound' : ∀ B ∈ K, ∃ M > 0, ∀ t : NNReal,
      ‖S.boundedPerturbation B t‖ ≤ M * Real.exp (0 * t) := by
    simpa only [zero_mul, Real.exp_zero, mul_one] using hbound
  simpa only [zero_add] using
    S.exists_uniform_boundedPerturbation_bound hK hbound' hε

/-- The same uniformization for a continuous bounded-operator family indexed by a compact set.
This is the form used for compact frequency regions in Lemmas 2.3 and 2.4. -/
theorem exists_uniform_boundedPerturbation_bound_on (S : C0Semigroup ℂ E)
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    {B : P → E →L[ℂ] E} (hB : ContinuousOn B K) {ω : ℝ}
    (hbound : ∀ p ∈ K, ∃ M > 0, ∀ t : NNReal,
      ‖S.boundedPerturbation (B p) t‖ ≤ M * Real.exp (ω * t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ p ∈ K, ∀ t : NNReal,
      ‖S.boundedPerturbation (B p) t‖ ≤ C * Real.exp ((ω + ε) * t) := by
  have hpoint : ∀ A ∈ B '' K, ∃ M > 0, ∀ t : NNReal,
      ‖S.boundedPerturbation A t‖ ≤ M * Real.exp (ω * t) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hbound p hp
  obtain ⟨C, hC, hCb⟩ :=
    S.exists_uniform_boundedPerturbation_bound (hK.image_of_continuousOn hB) hpoint hε
  exact ⟨C, hC, fun p hp t ↦ hCb (B p) (mem_image_of_mem B hp) t⟩

end

end C0Semigroup
