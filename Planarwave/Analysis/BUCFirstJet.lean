/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

/-!
# Closed first-derivative graphs in spatial BUC

A jet is a value paired with a proposed Fréchet derivative. The subspace
of genuine derivative jets is closed under uniform limits and invariant
under heat flow. This allows Volterra series to be differentiated without
assuming regularity of their limits in advance.
-/

open Filter Set

namespace Planarwave

noncomputable section

section Jets

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The value and first Fréchet derivative at one spatial point. -/
abbrev FirstJet (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := F × (E →L[ℝ] F)

def firstJetValue : BUC E (FirstJet E F) →L[ℝ] BUC E F :=
  BUC.postcompCLM (ContinuousLinearMap.fst ℝ F (E →L[ℝ] F))

def firstJetDerivative : BUC E (FirstJet E F) →L[ℝ] BUC E (E →L[ℝ] F) :=
  BUC.postcompCLM (ContinuousLinearMap.snd ℝ F (E →L[ℝ] F))

@[simp] theorem firstJetValue_apply (u : BUC E (FirstJet E F)) (x : E) :
    firstJetValue u x = (u x).1 := rfl

@[simp] theorem firstJetDerivative_apply (u : BUC E (FirstJet E F)) (x : E) :
    firstJetDerivative u x = (u x).2 := rfl

/-- Bundle two BUC fields as a BUC jet; no derivative identity is assumed. -/
def firstJetBUC (f : BUC E F) (f' : BUC E (E →L[ℝ] F)) : BUC E (FirstJet E F) :=
  BUC.postcompCLM (ContinuousLinearMap.inl ℝ F (E →L[ℝ] F)) f +
    BUC.postcompCLM (ContinuousLinearMap.inr ℝ F (E →L[ℝ] F)) f'

@[simp] theorem firstJetBUC_apply (f : BUC E F) (f' : BUC E (E →L[ℝ] F)) (x : E) :
    firstJetBUC f f' x = (f x, f' x) := by simp [firstJetBUC]

@[simp] theorem firstJetValue_firstJetBUC (f : BUC E F) (f' : BUC E (E →L[ℝ] F)) :
    firstJetValue (firstJetBUC f f') = f := by ext x; simp

@[simp] theorem firstJetDerivative_firstJetBUC (f : BUC E F) (f' : BUC E (E →L[ℝ] F)) :
    firstJetDerivative (firstJetBUC f f') = f' := by ext x; simp

theorem continuous_firstJetBUC :
    Continuous (fun p : BUC E F × BUC E (E →L[ℝ] F) ↦ firstJetBUC p.1 p.2) :=
  ((BUC.postcompCLM (ContinuousLinearMap.inl ℝ F (E →L[ℝ] F))).continuous.comp continuous_fst).add
    ((BUC.postcompCLM (ContinuousLinearMap.inr ℝ F (E →L[ℝ] F))).continuous.comp continuous_snd)

/-- The linear subspace of jets satisfying the actual derivative identity. -/
def firstJetSubmodule : Submodule ℝ (BUC E (FirstJet E F)) where
  carrier u := ∀ x, HasFDerivAt (firstJetValue u) (firstJetDerivative u x) x
  zero_mem' := by intro x; simpa using! hasFDerivAt_const (𝕜 := ℝ) (0 : F) x
  add_mem' := by
    intro u v hu hv x
    simpa only [map_add, BUC.add_apply] using! (hu x).add (hv x)
  smul_mem' := by
    intro c u hu x
    simpa only [map_smul, BUC.smul_apply] using! (hu x).const_smul c

/-- Uniform convergence of values and derivatives preserves the derivative
identity, so the first-jet subspace is closed. -/
theorem isClosed_firstJetSubmodule :
    IsClosed (firstJetSubmodule (E := E) (F := F) : Set (BUC E (FirstJet E F))) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u p hu hup
  have hv := (firstJetValue.continuous.tendsto p).comp hup
  have hd := (firstJetDerivative.continuous.tendsto p).comp hup
  have hvu := BUC.tendsto_iff_tendstoUniformly.mp hv
  have hdu := BUC.tendsto_iff_tendstoUniformly.mp hd
  intro x
  exact hasFDerivAt_of_tendstoUniformly hdu (fun n y ↦ hu n y)
    (fun y ↦ hvu.tendsto_at y) x

end Jets

section Heat

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Heat flow preserves genuine derivative jets, by commutation with the
spatial derivative. No positive-time assumption is needed here. -/
theorem heatFlowBUC_mem_firstJetSubmodule (a t : ℝ) (u : BUC E (FirstJet E F))
    (hu : u ∈ firstJetSubmodule) : heatFlowBUC a t u ∈ firstJetSubmodule := by
  intro x
  change HasFDerivAt
    (BUC.postcompCLM (ContinuousLinearMap.fst ℝ F (E →L[ℝ] F)) (heatFlowBUC a t u))
    (BUC.postcompCLM (ContinuousLinearMap.snd ℝ F (E →L[ℝ] F)) (heatFlowBUC a t u) x) x
  rw [← heatFlowBUC_postcomp, ← heatFlowBUC_postcomp]
  exact hasFDerivAt_heatFlow_of_hasFDerivAt a t (firstJetValue u) (firstJetDerivative u) hu x

end Heat

end

end Planarwave
