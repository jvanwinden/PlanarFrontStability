/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCMixedDerivatives

@[expose] public section

/-!
# Recovering time derivatives in the BUC norm

For a BUC-valued trajectory and a continuous BUC-valued candidate derivative,
the pointwise time derivative identities imply differentiability in the BUC
norm. The proof integrates on a compact interval inside the open time domain
and uses the Banach-valued fundamental theorem of calculus.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Planarwave.BUC

noncomputable section

variable {E F : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A continuous pointwise time derivative of a BUC trajectory is its actual
derivative in the supremum norm, locally on an open time interval. -/
theorem hasDerivAt_of_pointwise_on_Ioo {a b t : ℝ} {u v : ℝ → BUC E F}
    (hu : ContinuousOn u (Ioo a b)) (hv : ContinuousOn v (Ioo a b))
    (hpoint : ∀ r ∈ Ioo a b, ∀ x, HasDerivAt (fun s ↦ u s x) (v r x) r)
    (ht : t ∈ Ioo a b) : HasDerivAt u (v t) t := by
  let a' := (a + t) / 2
  let b' := (t + b) / 2
  have haa' : a < a' := by dsimp only [a']; linarith [ht.1]
  have ha't : a' < t := by dsimp only [a']; linarith [ht.1]
  have htb' : t < b' := by dsimp only [b']; linarith [ht.2]
  have hb'b : b' < b := by dsimp only [b']; linarith [ht.2]
  have hsub : Icc a' b' ⊆ Ioo a b :=
    fun r hr ↦ ⟨haa'.trans_le hr.1, hr.2.trans_lt hb'b⟩
  have hvc : ContinuousOn v (Icc a' b') := hv.mono hsub
  have heq (s : ℝ) (hs : s ∈ Icc a' b') : (∫ r in a'..s, v r) = u s - u a' := by
    have hsub' : Icc a' s ⊆ Ioo a b :=
      (Icc_subset_Icc le_rfl hs.2).trans hsub
    have hvint : IntervalIntegrable v volume a' s :=
      (hv.mono hsub').intervalIntegrable_of_Icc hs.1
    apply BUC.ext
    intro x
    change (BUC.evalCLM (𝕜 := ℝ) x) (∫ r in a'..s, v r) = u s x - u a' x
    rw [← (BUC.evalCLM (𝕜 := ℝ) x).intervalIntegral_comp_comm hvint]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      ((BUC.evalCLM (𝕜 := ℝ) x).continuous.comp_continuousOn (hu.mono hsub'))
      (fun r hr ↦ hpoint r (hsub' (Ioo_subset_Icc_self hr)) x)
      (((BUC.evalCLM (𝕜 := ℝ) x).continuous.comp_continuousOn
        (hv.mono hsub')).intervalIntegrable_of_Icc hs.1)
  have hnhds : Icc a' b' ∈ 𝓝 t := Icc_mem_nhds ha't htb'
  have hi := intervalIntegral.integral_hasDerivAt_right
    ((hvc.mono (Icc_subset_Icc le_rfl htb'.le)).intervalIntegrable_of_Icc ha't.le)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hv t ht)
    (hv.continuousAt (isOpen_Ioo.mem_nhds ht))
  apply (hi.add_const (u a')).congr_of_eventuallyEq
  filter_upwards [hnhds] with s hs
  rw [heq s hs, sub_add_cancel]

end

end Planarwave.BUC
