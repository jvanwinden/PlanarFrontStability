/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCJointContinuity
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Joint spacetime calculus from continuous partial derivatives

The time derivative and the spatial Fréchet derivative assemble into the
joint derivative. This is used after parabolic smoothing: BUC continuity
of the derivative fields supplies joint continuity on each positive-time
slab. A higher-order version keeps the regularity of the two partial
derivative fields explicit for the subsequent spacetime bootstrap.
-/

open Filter Set
open scoped Topology ContDiff

namespace Planarwave

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The spacetime derivative sends `(τ,h)` to `τ • v + q h`. -/
def spacetimeFDeriv (v : F) (q : E →L[ℝ] F) : ℝ × E →L[ℝ] F :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight v).coprod q

@[simp]
theorem spacetimeFDeriv_apply (v : F) (q : E →L[ℝ] F) (w : ℝ × E) :
    spacetimeFDeriv v q w = w.1 • v + q w.2 := rfl

/-- Jointly continuous partial derivatives give the strict joint derivative. -/
theorem hasStrictFDerivAt_spacetime {s : Set ℝ} (hs : IsOpen s)
    {u v : ℝ → E → F} {q : ℝ → E → E →L[ℝ] F}
    (hv : ContinuousOn (fun p : ℝ × E ↦ v p.1 p.2) (s ×ˢ univ))
    (hq : ContinuousOn (fun p : ℝ × E ↦ q p.1 p.2) (s ×ˢ univ))
    (htime : ∀ t ∈ s, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t)
    (hspace : ∀ t ∈ s, ∀ x, HasFDerivAt (u t) (q t x) x)
    {p : ℝ × E} (hp : p.1 ∈ s) :
    HasStrictFDerivAt (fun z : ℝ × E ↦ u z.1 z.2)
      (spacetimeFDeriv (v p.1 p.2) (q p.1 p.2)) p := by
  have hnhds : s ×ˢ (univ : Set E) ∈ 𝓝 p := (hs.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩
  have hvc := hv.continuousAt hnhds
  have hqc := hq.continuousAt hnhds
  apply hasStrictFDerivAt_uncurry_coprod
    (f₁ := fun t x ↦ (ContinuousLinearMap.id ℝ ℝ).smulRight (v t x))
    (f₂ := q)
  · filter_upwards [hnhds] with z hz
    exact (htime z.1 hz.1 z.2).hasFDerivAt
  · filter_upwards [hnhds] with z hz
    exact hspace z.1 hz.1 z.2
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ)).continuous.continuousAt.comp hvc
  · exact hqc

/-- Higher joint regularity follows from the joint regularity of both
partial derivative fields, with no separate mixed-derivative assumption. -/
theorem contDiffOn_succ_spacetime {s : Set ℝ} (hs : IsOpen s) (k : ℕ)
    {u v : ℝ → E → F} {q : ℝ → E → E →L[ℝ] F}
    (hv : ContDiffOn ℝ k (fun p : ℝ × E ↦ v p.1 p.2) (s ×ˢ univ))
    (hq : ContDiffOn ℝ k (fun p : ℝ × E ↦ q p.1 p.2) (s ×ˢ univ))
    (htime : ∀ t ∈ s, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t)
    (hspace : ∀ t ∈ s, ∀ x, HasFDerivAt (u t) (q t x) x) :
    ContDiffOn ℝ (k + 1 : ℕ) (fun p : ℝ × E ↦ u p.1 p.2) (s ×ˢ univ) := by
  have hd : ContDiffOn ℝ k (fun p : ℝ × E ↦ spacetimeFDeriv (v p.1 p.2) (q p.1 p.2))
      (s ×ˢ univ) := by
    simp only [spacetimeFDeriv, ← ContinuousLinearMap.comp_fst_add_comp_snd]
    have ht := (ContinuousLinearMap.smulRightL ℝ ℝ F
      (ContinuousLinearMap.id ℝ ℝ)).contDiff.comp_contDiffOn hv
    exact (ht.clm_comp contDiffOn_const).add (hq.clm_comp contDiffOn_const)
  rw [Nat.cast_add, Nat.cast_one,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hs.prod isOpen_univ).uniqueDiffOn]
  refine ⟨by simp, _, hd, fun p hp ↦ ?_⟩
  exact (hasStrictFDerivAt_spacetime hs hv.continuousOn hq.continuousOn htime hspace hp.1).hasFDerivAt.hasFDerivWithinAt

/-- BUC-continuous derivative fields imply joint `C¹` regularity on an
open time slab. Time derivatives are only assumed pointwise in space. -/
theorem contDiffOn_one_buc_spacetime {s : Set ℝ} (hs : IsOpen s)
    {u v : ℝ → BUC E F} {q : ℝ → BUC E (E →L[ℝ] F)}
    (hv : ContinuousOn v s) (hq : ContinuousOn q s)
    (htime : ∀ t ∈ s, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t)
    (hspace : ∀ t ∈ s, ∀ x, HasFDerivAt (u t) (q t x) x) :
    ContDiffOn ℝ 1 (fun p : ℝ × E ↦ u p.1 p.2) (s ×ˢ univ) := by
  simpa only [zero_add, Nat.cast_one] using contDiffOn_succ_spacetime hs 0
    (contDiffOn_zero.mpr (BUC.continuousOn_uncurry hv))
    (contDiffOn_zero.mpr (BUC.continuousOn_uncurry hq)) htime hspace

end

end Planarwave
