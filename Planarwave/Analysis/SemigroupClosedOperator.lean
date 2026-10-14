/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ClosedOperatorResolvent
public import Planarwave.Analysis.SemigroupLaplace

@[expose] public section

/-!
# From a semigroup generator to the fixed-domain resolvent

When a closed operator represents the full generator graph, the Laplace inverse proves
bijectivity of its resolvent map. Our operator convention is `A - z I`, so its ambient inverse
is the negative of the semigroup Laplace transform, which inverts `z I - A`.
-/

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

/-- The Laplace inverse gives resolvent bijectivity in the half-plane of the growth bound. -/
theorem isInResolvent_of_semigroup_bound (A : ClosedOperator ℂ E Dom) (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {M ω : ℝ} (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < z.re) : A.IsInResolvent z := by
  have hleft (v : Dom) : S.laplaceResolvent hbound z hz
      (z • A.inclusion v - A.operator v) = A.inclusion v :=
    ((hgen _ _).mpr ⟨v, rfl, rfl⟩).laplaceResolvent_apply hbound z hz
  constructor
  · intro v w hvw
    apply A.inclusion_injective
    rw [← hleft v, ← hleft w]
    apply congrArg
    change A.operator v - z • A.inclusion v = A.operator w - z • A.inclusion w at hvw
    simpa only [neg_sub] using congrArg Neg.neg hvw
  · intro x
    obtain ⟨v, hv, hAv⟩ := (hgen _ _).mp (S.hasGeneratorAt_laplaceResolvent hbound z hz (-x))
    refine ⟨v, ?_⟩
    change A.operator v - z • A.inclusion v = x
    rw [hAv, hv]
    abel

/-- The fixed-domain resolvent inverse, after inclusion in the ambient space, is the negative
Laplace transform. This also fixes the sign convention in later contour formulas. -/
theorem inclusion_resolventInverse_eq_neg_laplace (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {M ω : ℝ} (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < z.re) (hres : A.IsInResolvent z) :
    A.inclusion.comp (A.resolventInverse z hres) = -S.laplaceResolvent hbound z hz := by
  ext x
  let v := A.resolventInverse z hres x
  have hAv : A.operator v - z • A.inclusion v = x := A.resolventMap_resolventInverse z hres x
  have hleft := ((hgen _ _).mpr ⟨v, rfl, rfl⟩).laplaceResolvent_apply hbound z hz
  have hneg : z • A.inclusion v - A.operator v = -x := by
    rw [← hAv]
    abel
  rw [hneg, map_neg] at hleft
  exact hleft.symm

/-- The ambient operator norm of the closed-operator resolvent has the Laplace bound. -/
theorem norm_inclusion_resolventInverse_le (A : ClosedOperator ℂ E Dom) (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {M ω : ℝ} (hM : 0 ≤ M) (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < z.re) (hres : A.IsInResolvent z) :
    ‖A.inclusion.comp (A.resolventInverse z hres)‖ ≤ M / (z.re - ω) := by
  rw [A.inclusion_resolventInverse_eq_neg_laplace S hgen hbound z hz hres, norm_neg]
  exact S.norm_laplaceResolvent_le hM hbound z hz

/-- The total ambient resolvent agrees with the Laplace transform throughout the growth
half-plane. In particular no arbitrary inverse choice enters contour integrals there. -/
theorem ambientResolvent_eq_neg_laplace (A : ClosedOperator ℂ E Dom) (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {M ω : ℝ} (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < z.re) :
    A.ambientResolvent z = -S.laplaceResolvent hbound z hz := by
  have hres := A.isInResolvent_of_semigroup_bound S hgen hbound z hz
  rw [A.ambientResolvent_eq hres]
  exact A.inclusion_resolventInverse_eq_neg_laplace S hgen hbound z hz hres

end

end Planarwave.ClosedOperator
