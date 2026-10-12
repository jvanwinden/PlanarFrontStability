/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupCompactBounds
public import Planarwave.Analysis.SemigroupSpectralDamping

@[expose] public section

/-!
# Compact-family uniformization on varying spectral complements

The individual complementary bounds in Lemma 2.3 are uniformized using the paper's
appendix lemma. Extending each complementary semigroup by the same scalar exponential
on its critical eigenline places the entire family on the original fixed space.
The extension is a continuous bounded perturbation, and its complementary part is
exactly the original one. The only rate loss is the appendix's arbitrary `ε > 0`.
-/

open Set

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The appendix uniform bound for a compact continuous family of complementary spectral
subspaces. The subspaces may vary with the parameter. -/
theorem exists_uniform_complement_bound_on (S : C0Semigroup ℂ E)
    {I : Type*} [TopologicalSpace I] {K : Set I} (hK : IsCompact K)
    {B P : I → E →L[ℂ] E} {ζ : I → ℂ}
    (hB : ContinuousOn B K) (hPc : ContinuousOn P K) (hζ : ContinuousOn ζ K)
    (hP : ∀ p ∈ K, ∀ x, P p (P p x) = P p x)
    (hcomm : ∀ p ∈ K, ∀ t : NNReal,
      (S.boundedPerturbation (B p) t).comp (P p) =
        (P p).comp (S.boundedPerturbation (B p) t))
    (heig : ∀ p ∈ K, ∀ x,
      (S.boundedPerturbation (B p)).HasGeneratorAt (P p x) (ζ p • P p x))
    {ω : ℝ} (hpoint : ∀ p ∈ K, ∃ M > 0, ∀ t : NNReal,
      ‖(S.boundedPerturbation (B p) t).comp (ContinuousLinearMap.id ℂ E - P p)‖ ≤
        M * Real.exp (ω * t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ M > 0, ∀ p ∈ K, ∀ t : NNReal,
      ‖(S.boundedPerturbation (B p) t).comp (ContinuousLinearMap.id ℂ E - P p)‖ ≤
        M * Real.exp ((ω + ε) * t) := by
  let C : I → E →L[ℂ] E := fun p ↦ B p + ((ω : ℂ) - ζ p) • P p
  have hC : ContinuousOn C K := hB.add ((continuousOn_const.sub hζ).smul hPc)
  have hCb : ∀ p ∈ K, ∃ M > 0, ∀ t : NNReal,
      ‖S.boundedPerturbation (C p) t‖ ≤ M * Real.exp (ω * t) := by
    intro p hp
    obtain ⟨M, hM, hb⟩ := hpoint p hp
    refine ⟨M + ‖P p‖, by positivity, ?_⟩
    intro t
    have h := (S.boundedPerturbation (B p)).norm_boundedPerturbation_spectral_le
      (P p) (hP p hp) (hcomm p hp) (heig p hp) (ρ := ω) le_rfl hb t
    rw [S.boundedPerturbation_add] at h
    exact h
  obtain ⟨M, hM, hb⟩ := S.exists_uniform_boundedPerturbation_bound_on hK hC hCb hε
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn
    (continuousOn_const.sub hPc : ContinuousOn (fun p ↦ ContinuousLinearMap.id ℂ E - P p) K)
  let L' := max L 0 + 1
  have hL' : 0 < L' := by dsimp [L']; positivity
  refine ⟨M * L', mul_pos hM hL', ?_⟩
  intro p hp t
  have heq : (S.boundedPerturbation (C p) t).comp (ContinuousLinearMap.id ℂ E - P p) =
      (S.boundedPerturbation (B p) t).comp (ContinuousLinearMap.id ℂ E - P p) := by
    have h := (S.boundedPerturbation (B p)).boundedPerturbation_spectral_comp_complement
      (P p) (hP p hp) (hcomm p hp) ((ω : ℂ) - ζ p) t
    rw [S.boundedPerturbation_add] at h
    exact h
  rw [← heq]
  calc
    ‖(S.boundedPerturbation (C p) t).comp (ContinuousLinearMap.id ℂ E - P p)‖ ≤
        ‖S.boundedPerturbation (C p) t‖ * ‖ContinuousLinearMap.id ℂ E - P p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (M * Real.exp ((ω + ε) * t)) * L' := by
      apply mul_le_mul (hb p hp t) _ (norm_nonneg _) (by positivity)
      exact (hL p hp).trans (by dsimp [L']; linarith [le_max_left L 0])
    _ = _ := by ring

end

end C0Semigroup
