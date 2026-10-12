/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ClosedOperator
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# The operator-valued resolvent on the ambient Banach space

The resolvent set is open, and the inverse is holomorphic in the graph norm and in the
ambient operator norm. We use the paper's `A - z I` sign convention, giving
`R(z) - R(w) = (z - w) R(w) R(z)`. The total inverse is zero off the resolvent set;
regularity is asserted only at resolvent points.
-/

open Filter Set
open scoped ContDiff Topology

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

theorem isInResolvent_iff_isInvertible (A : ClosedOperator ℂ E Dom) (z : ℂ) :
    A.IsInResolvent z ↔ (A.resolventMap z).IsInvertible := by
  constructor
  · intro hz
    exact ⟨A.resolventEquiv z hz, rfl⟩
  · rintro ⟨e, he⟩
    change Function.Bijective (A.resolventMap z)
    rw [← he]
    exact e.bijective

/-- Total graph-domain inverse, agreeing with the bounded resolvent on its resolvent set. -/
def graphResolvent (A : ClosedOperator ℂ E Dom) (z : ℂ) : E →L[ℂ] Dom :=
  (A.resolventMap z).inverse

/-- The resolvent as a bounded operator on the ambient state space. -/
def ambientResolvent (A : ClosedOperator ℂ E Dom) (z : ℂ) : E →L[ℂ] E :=
  A.inclusion.comp (A.graphResolvent z)

theorem graphResolvent_eq (A : ClosedOperator ℂ E Dom) {z : ℂ} (hz : A.IsInResolvent z) :
    A.graphResolvent z = A.resolventInverse z hz := by
  exact ContinuousLinearMap.inverse_equiv (A.resolventEquiv z hz)

theorem ambientResolvent_eq (A : ClosedOperator ℂ E Dom) {z : ℂ} (hz : A.IsInResolvent z) :
    A.ambientResolvent z = A.inclusion.comp (A.resolventInverse z hz) := by
  rw [ambientResolvent, A.graphResolvent_eq hz]

/-- The common-domain resolvent map is affine, hence holomorphic in the spectral parameter. -/
theorem contDiff_resolventMap (A : ClosedOperator ℂ E Dom) : ContDiff ℂ ω A.resolventMap := by
  unfold resolventMap
  fun_prop

/-- Resolvent points form an open set in the complex plane. -/
theorem isOpen_resolventSet (A : ClosedOperator ℂ E Dom) : IsOpen A.resolventSet := by
  have heq : A.resolventSet = A.resolventMap ⁻¹'
      range ((↑) : (Dom ≃L[ℂ] E) → Dom →L[ℂ] E) := by
    ext z
    exact A.isInResolvent_iff_isInvertible z
  rw [heq]
  exact ContinuousLinearEquiv.isOpen.preimage A.contDiff_resolventMap.continuous

/-- The spectrum of the closed operator is closed. -/
theorem isClosed_spectrum (A : ClosedOperator ℂ E Dom) : IsClosed A.spectrum :=
  A.isOpen_resolventSet.isClosed_compl

/-- The resolvent is holomorphic even as a map into the graph-norm domain operators. -/
theorem contDiffAt_graphResolvent (A : ClosedOperator ℂ E Dom) {z : ℂ}
    (hz : A.IsInResolvent z) : ContDiffAt ℂ ω A.graphResolvent z := by
  exact ((A.isInResolvent_iff_isInvertible z).mp hz).contDiffAt_map_inverse.comp z
    A.contDiff_resolventMap.contDiffAt

/-- The ambient operator-valued resolvent is holomorphic on its resolvent set. -/
theorem contDiffAt_ambientResolvent (A : ClosedOperator ℂ E Dom) {z : ℂ}
    (hz : A.IsInResolvent z) : ContDiffAt ℂ ω A.ambientResolvent z :=
  contDiffAt_const.clm_comp (A.contDiffAt_graphResolvent hz)

/-- The first resolvent identity with the `A - z I` sign convention. -/
theorem ambientResolvent_sub (A : ClosedOperator ℂ E Dom) {z w : ℂ}
    (hz : A.IsInResolvent z) (hw : A.IsInResolvent w) :
    A.ambientResolvent z - A.ambientResolvent w =
      (z - w) • (A.ambientResolvent w).comp (A.ambientResolvent z) := by
  have hshift (v : Dom) : A.resolventMap w v = A.resolventMap z v + (z - w) • A.inclusion v := by
    simp only [resolventMap_apply, sub_smul]
    abel
  ext x
  have hi := congrArg (A.resolventInverse w hw) (hshift (A.resolventInverse z hz x))
  rw [A.resolventInverse_resolventMap, A.resolventMap_resolventInverse, map_add, map_smul] at hi
  have hi' := congrArg A.inclusion hi
  simp only [map_add, map_smul] at hi'
  simp only [A.ambientResolvent_eq hz, A.ambientResolvent_eq hw, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply]
  exact sub_eq_iff_eq_add'.mpr hi'

/-- The derivative of the ambient resolvent, in the `A - z I` convention, is its square. -/
theorem hasDerivAt_ambientResolvent (A : ClosedOperator ℂ E Dom) {z : ℂ}
    (hz : A.IsInResolvent z) :
    HasDerivAt A.ambientResolvent ((A.ambientResolvent z).comp (A.ambientResolvent z)) z := by
  have hc : ContinuousAt (fun w ↦ (A.ambientResolvent z).comp (A.ambientResolvent w)) z :=
    continuousAt_const.clm_comp (A.contDiffAt_ambientResolvent hz).continuousAt
  have hres' : ∀ᶠ w in 𝓝 z, A.IsInResolvent w := A.isOpen_resolventSet.mem_nhds hz
  have hres := hres'.filter_mono (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
  rw [hasDerivAt_iff_tendsto_slope]
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hres, self_mem_nhdsWithin] with w hw hwne
  rw [slope, vsub_eq_sub, A.ambientResolvent_sub hw hz, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hwne), one_smul]

end

end Planarwave.ClosedOperator
