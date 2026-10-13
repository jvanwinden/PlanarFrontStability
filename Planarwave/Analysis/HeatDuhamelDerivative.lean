/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCFirstJet
public import Planarwave.Analysis.HeatVolterraInvariant

@[expose] public section

/-!
# Spatial differentiation of heat Duhamel integrals

Bounded linear maps commute with the BUC-valued Duhamel integral.
Integrating in the closed first-jet subspace then justifies spatial
differentiation, including at the initial time.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem heatDuhamel_postcomp (a : ℝ) (L : F →L[ℝ] G)
    {f : ℝ → BUC E F} (hf : Continuous f) (t : ℝ) :
    heatDuhamel a (fun r ↦ BUC.postcompCLM L (f r)) t =
      BUC.postcompCLM L (heatDuhamel a f t) := by
  simp only [heatDuhamel, heatFlowBUC_postcomp]
  exact (BUC.postcompCLM L).intervalIntegral_comp_comm
    (((continuous_heatDuhamel_integrand a hf).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)

theorem firstJetValue_heatDuhamel (a : ℝ)
    {f : ℝ → BUC E (FirstJet E F)} (hf : Continuous f) (t : ℝ) :
    firstJetValue (heatDuhamel a f t) = heatDuhamel a (fun r ↦ firstJetValue (f r)) t :=
  (heatDuhamel_postcomp a (ContinuousLinearMap.fst ℝ F (E →L[ℝ] F)) hf t).symm

theorem firstJetDerivative_heatDuhamel (a : ℝ)
    {f : ℝ → BUC E (FirstJet E F)} (hf : Continuous f) (t : ℝ) :
    firstJetDerivative (heatDuhamel a f t) =
      heatDuhamel a (fun r ↦ firstJetDerivative (f r)) t :=
  (heatDuhamel_postcomp a (ContinuousLinearMap.snd ℝ F (E →L[ℝ] F)) hf t).symm

/-- A continuous BUC derivative of the source gives the actual spatial
derivative of its heat Duhamel response. -/
theorem hasFDerivAt_heatDuhamel (a : ℝ) {f : ℝ → BUC E F}
    {f' : ℝ → BUC E (E →L[ℝ] F)} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ r x, HasFDerivAt (f r) (f' r x) x) (t : ℝ) (x : E) :
    HasFDerivAt (heatDuhamel a f t) (heatDuhamel a f' t x) x := by
  let j := fun r ↦ firstJetBUC (f r) (f' r)
  have hj : Continuous j := continuous_firstJetBUC.comp (hf.prodMk hf')
  have hmem : ∀ r, j r ∈ firstJetSubmodule := by
    intro r y
    simpa [j] using hderiv r y
  have hm := heatDuhamel_mem_submodule a firstJetSubmodule isClosed_firstJetSubmodule
    (heatFlowBUC_mem_firstJetSubmodule a) hj hmem t
  have hd := hm x
  rw [firstJetValue_heatDuhamel a hj, firstJetDerivative_heatDuhamel a hj] at hd
  simpa [j] using hd

end

end Planarwave
