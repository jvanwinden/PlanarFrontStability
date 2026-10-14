/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatVolterra

@[expose] public section

/-!
# Closed invariant subspaces for heat Volterra equations

The Volterra series remains in any closed subspace preserved by the heat
flow and the time-dependent coefficient. Applied to derivative jets, this
proves regularity of the solution, not just a formal differentiated equation.
-/

open Filter MeasureTheory Set Topology
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

theorem closedSubmodule_intervalIntegral_mem
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (K : Submodule ℝ V) (hK : IsClosed (K : Set V))
    {f : ℝ → V} (hf : Continuous f) (hmem : ∀ r, f r ∈ K) (a b : ℝ) :
    (∫ r in a..b, f r) ∈ K := by
  let : IsClosed (K : Set V) := hK
  let fK : ℝ → K := fun r ↦ ⟨f r, hmem r⟩
  have hfK : Continuous fK := hf.subtype_mk hmem
  have heq := K.subtypeL.intervalIntegral_comp_comm (μ := volume) (hfK.intervalIntegrable a b)
  change (∫ r in a..b, K.subtypeL (fK r)) ∈ K
  rw [heq]
  exact (∫ r in a..b, fK r).property

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem heatDuhamel_mem_submodule (a : ℝ)
    (K : Submodule ℝ (BUC E F)) (hK : IsClosed (K : Set (BUC E F)))
    (hheat : ∀ t u, u ∈ K → heatFlowBUC a t u ∈ K)
    {f : ℝ → BUC E F} (hf : Continuous f) (hmem : ∀ r, f r ∈ K) (t : ℝ) :
    heatDuhamel a f t ∈ K := by
  apply closedSubmodule_intervalIntegral_mem K hK
    ((continuous_heatDuhamel_integrand a hf).comp (continuous_const.prodMk continuous_id))
  intro r
  exact hheat (t - r) (f r) (hmem r)

theorem heatVolterraPath_mem_submodule (a : ℝ) {T : NNReal}
    (K : Submodule ℝ (BUC E F)) (hK : IsClosed (K : Set (BUC E F)))
    (hheat : ∀ t u, u ∈ K → heatFlowBUC a t u ∈ K)
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (hB : ∀ t u, u ∈ K → B t u ∈ K)
    (u : TimePath (E := BUC E F) T) (hu : ∀ t, u t ∈ K) (t : Icc (0 : ℝ) (T : ℝ)) :
    heatVolterraPath a B u t ∈ K := by
  apply heatDuhamel_mem_submodule a K hK hheat
    ((continuous_extendTimePath B).clm_apply (continuous_extendTimePath u))
  intro r
  exact hB _ _ (hu _)

/-- The convergent Volterra series lies in the closed invariant subspace
at every time. There is no small-time restriction. -/
theorem exists_heatVolterraPath_mem_submodule (a : ℝ) {T : NNReal}
    (K : Submodule ℝ (BUC E F)) (hK : IsClosed (K : Set (BUC E F)))
    (hheat : ∀ t u, u ∈ K → heatFlowBUC a t u ∈ K)
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (hB : ∀ t u, u ∈ K → B t u ∈ K)
    (f : TimePath (E := BUC E F) T) (hf : ∀ t, f t ∈ K) :
    ∃ u : TimePath (E := BUC E F) T,
      (∀ t, u t = f t + heatVolterraPath a B u t) ∧ ∀ t, u t ∈ K := by
  let V := heatVolterraOperator a B
  let R := ∑' n : ℕ, V ^ n
  let : IsTopologicalRing (TimePath (E := BUC E F) T →L[ℝ] TimePath (E := BUC E F) T) :=
    NonUnitalSeminormedRing.toIsTopologicalRing
      (α := TimePath (E := BUC E F) T →L[ℝ] TimePath (E := BUC E F) T)
  have hs : Summable (fun n : ℕ ↦ V ^ n) := summable_heatVolterraOperator_pow a B
  refine ⟨R f, ?_, ?_⟩
  · intro t
    have h := congrArg (fun L : TimePath (E := BUC E F) T →L[ℝ]
      TimePath (E := BUC E F) T ↦ L f t) hs.one_sub_mul_tsum_pow
    change R f t - heatVolterraPath a B (R f) t = f t at h
    exact sub_eq_iff_eq_add.mp h
  · have hp : ∀ n : ℕ, ∀ t, ((V ^ n) f) t ∈ K := by
      intro n
      induction n with
      | zero => simpa using hf
      | succ n ih =>
        intro t
        simpa only [pow_succ', mul_apply_eq_comp, V, heatVolterraOperator_apply] using
          heatVolterraPath_mem_submodule a K hK hheat B hB ((V ^ n) f) ih t
    intro t
    have hsum : HasSum (fun n : ℕ ↦ ((V ^ n) f) t) (R f t) :=
      (ContinuousMap.evalCLM (M := BUC E F) ℝ t).hasSum
        ((ContinuousLinearMap.apply ℝ (TimePath (E := BUC E F) T) f).hasSum hs.hasSum)
    apply hK.mem_of_tendsto hsum
    exact Filter.Eventually.of_forall (fun s : Finset ℕ ↦ K.sum_mem (fun n _ ↦ hp n t))

end

end Planarwave
