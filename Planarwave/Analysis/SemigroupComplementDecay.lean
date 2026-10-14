/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ClosedOperatorRestriction
public import Planarwave.Analysis.SemigroupSpectralGrowth

@[expose] public section

/-!
# Spectral-gap decay on the complementary subspace

The proof of the first estimate of Lemma 2.3 first restricts to the complementary
spectral subspace and then applies equality of spectral and growth bounds there.
This file carries out that step, including the restricted generator and resolvent.
The prefactor here is individual, not yet uniform in a frequency parameter.
-/

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

/-- Removing a simple spectral eigenline exposes the complementary spectral gap as a
semigroup decay rate. Every hypothesis concerns the original generator and its splitting. -/
theorem exists_complement_bound_of_sectorial_spectrum (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    (P : E →L[ℂ] E) {ζ : ℂ} (hP : ∀ x, P (P x) = P x)
    (hS : ∀ t : NNReal, ∀ x ∈ P.ker, S t x ∈ P.ker)
    (hleft : ∀ v, P (A.operator v) = ζ • P (A.inclusion v))
    (hlift : ∀ x, ∃ v, A.inclusion v = P x ∧ A.operator v = ζ • P x)
    (hker : ∀ v, A.resolventMap ζ v = 0 → P (A.inclusion v) = A.inclusion v)
    (hrange : ∀ y, P y = 0 → ∃ v, A.resolventMap ζ v = y)
    {a C₀ Ω s β : ℝ} (ha : 0 < a)
    (hsector : ∀ z : ℂ, Ω < z.re + a * |z.im| → A.IsInResolvent z ∧
      ‖A.ambientResolvent z‖ ≤ C₀ / (z.re + a * |z.im| - Ω))
    (hspec : ∀ z ∈ A.spectrum, z ≠ ζ → z.re ≤ s) (hβ : s < β) :
    ∃ M > 0, ∀ t : NNReal,
      ‖(S t).comp (ContinuousLinearMap.id ℂ E - P)‖ ≤ M * Real.exp (β * t) := by
  have hA : ∀ v, P (A.inclusion v) = 0 → P (A.operator v) = 0 := by
    intro v hv
    rw [hleft, hv, smul_zero]
  let T := S.restrictInvariant P.ker hS
  let B := A.restrictKernel P hA
  have hgenB : ∀ x y, T.HasGeneratorAt x y ↔ ∃ v, B.inclusion v = x ∧ B.operator v = y :=
    A.restrictKernel_hasGeneratorAt_iff P S hgen hS hA
  have hsectorB : ∀ z : ℂ, Ω < z.re + a * |z.im| →
      ‖B.ambientResolvent z‖ ≤ C₀ / (z.re + a * |z.im| - Ω) := by
    intro z hz
    exact (A.norm_ambientResolvent_restrictKernel_le P hA hleft hlift (hsector z hz).1).trans
      (hsector z hz).2
  have hspecB : ∀ z ∈ B.spectrum, z.re ≤ s := by
    intro z hz
    have h := A.spectrum_restrictKernel_subset P hA hP hleft hlift hker hrange hz
    exact hspec z h.1 h.2
  obtain ⟨M, hM, hb⟩ := B.exists_semigroup_bound_of_sectorial_spectrum T hgenB ha
    hsectorB hspecB hβ
  let Q := ContinuousLinearMap.id ℂ E - P
  have hQ : ∀ x, Q x ∈ P.ker := by
    intro x
    change P (x - P x) = 0
    rw [map_sub, hP, sub_self]
  refine ⟨M * (‖Q‖ + 1), by positivity, ?_⟩
  intro t
  calc
    ‖(S t).comp Q‖ ≤ ‖T t‖ * ‖Q‖ := S.norm_comp_le_restrictInvariant P.ker hS Q hQ t
    _ ≤ (M * Real.exp (β * t)) * (‖Q‖ + 1) :=
      mul_le_mul (hb t) (by linarith) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end

end Planarwave.ClosedOperator
