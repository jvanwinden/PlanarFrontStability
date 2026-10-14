/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfSecondRegularity
public import Planarwave.Analysis.HeatDuhamelTimeRegularity

@[expose] public section

/-!
# The classical forced Cole--Hopf equation

The mild solution constructed for the paper's delayed forcing is a
classical solution: it is spatially C² and its BUC-valued time derivative
is the heat generator minus the Cole--Hopf source. No time derivative
of the forcing or of the completed nonlinear source is assumed.
-/

open MeasureTheory Set
open scoped Laplacian
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance classicalColeHopfSecondTensorNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance classicalColeHopfSecondTensorNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance classicalColeHopfSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] E →L[ℝ] ℝ)
local instance classicalColeHopfSecondDerivativeNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) :=
  BUC.instNormedSpace (𝕜 := ℝ) (α := E) (E := E →L[ℝ] E →L[ℝ] ℝ)

/-- Two genuine spatial BUC derivatives, with continuous Hessian, turn
the mild equation into the classical equation in the BUC norm. -/
theorem IsForcedColeHopfMild.exists_time_derivative {a β T : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) (hg : ContinuousOn g (Icc 0 T))
    (q : ℝ → BUC E (E →L[ℝ] ℝ)) (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ))
    (hc : Continuous h)
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧
      HasFDerivAt (q t) (h t x) x) :
    ∃ v : ℝ → BUC E ℝ, Continuous v ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt ξ (v t) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ∀ x,
        v t x = a * Δ (ξ t : E → ℝ) x - (1 + β * ξ t x) * g t x := by
  let τ : NNReal := ⟨T, hT⟩
  let sp : TimePath (E := BUC E ℝ) τ :=
    ⟨fun t ↦ forcedColeHopfSource β (g t) (ξ t),
      continuousOn_iff_continuous_domRestrict.mp
        ((continuous_forcedColeHopfSource β).comp_continuousOn (hg.prodMk hξ.continuous))⟩
  let S := extendTimePath sp
  have hSc : Continuous S := continuous_extendTimePath sp
  have hSeq : ∀ t ∈ Icc 0 T, S t = forcedColeHopfSource β (g t) (ξ t) :=
    fun t ht ↦ extendTimePath_coe sp ⟨t, ht⟩
  let L : BUC E (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] BUC E ℝ :=
    BUC.postcompCLM (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ) (F := ℝ)
      (laplacianTraceCLM (E := E) (F := ℝ))
  let v := fun t ↦ a • L (h t) - S t
  have hvc : Continuous v := ((L.continuous.comp hc).const_smul a).sub hSc
  have hgen : ∀ t, convectiveGeneratorBUC a 0 (q t) (h t) = a • L (h t) := by
    intro t
    ext x
    simp [convectiveGeneratorBUC, L]
  have hright : ∀ s ∈ Ico 0 T, HasDerivWithinAt ξ (v s) (Ici s) s := by
    intro s hs
    have hdright := hasDerivWithinAt_heat_restart ha hs.2 (u := ξ) (f := fun r ↦ -S r)
      hSc.neg (q s) (h s) (fun x ↦ (hd s ⟨hs.1, hs.2.le⟩ x).1)
      (fun x ↦ (hd s ⟨hs.1, hs.2.le⟩ x).2) ?_
    · simpa only [hgen, sub_eq_add_neg, v] using hdright
    · intro t ht
      rw [hξ.restart ha.le hg hs.1 ht.1 ht.2]
      have hint : (∫ r in s..t, heatFlowBUC a (t - r) (-S r)) =
          -(∫ r in s..t, heatFlowBUC a (t - r) (forcedColeHopfSource β (g r) (ξ r))) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le ht.1] at hr
        dsimp only
        rw [hSeq r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩]
        exact (heatOperator a (t - r)).map_neg _
      rw [hint, sub_eq_add_neg]
  refine ⟨v, hvc, fun _ ht ↦
    hasDerivWithinAt_of_continuous_right_derivative hξ.continuous hvc hright ht, ?_⟩
  intro t ht x
  change a * laplacianTraceCLM (h t x) - S t x = _
  rw [hSeq t ht, forcedColeHopfSource_apply,
    laplacian_eq_trace_of_hasFDerivAt (ξ t) (q t) (h t)
      (fun y ↦ (hd t ht y).1) (fun y ↦ (hd t ht y).2)]
  ring

/-- The actual delayed-forcing mild solution has a continuous time
derivative field satisfying the forced heat equation. -/
theorem IsForcedColeHopfMild.delayed_exists_time_derivative {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ v : ℝ → BUC E ℝ, Continuous v ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt ξ (v t) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ∀ x,
        v t x = a * Δ (ξ t : E → ℝ) x -
          (1 + β * ξ t x) * delayedHeatForcing a p N t x := by
  obtain ⟨q, h, _, hc, hd⟩ := hξ.delayed_exists_buc_second_fderivative ha hT
  exact hξ.exists_time_derivative ha hT (continuous_delayedHeatForcing a p N).continuousOn q h hc hd

/-- Pointwise classical PDE at every interior time, derived from the
BUC-valued derivative rather than assumed as extra solution data. -/
theorem IsForcedColeHopfMild.delayed_hasDerivAt {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : E) :
    HasDerivAt (fun r ↦ ξ r x)
      (a * Δ (ξ t : E → ℝ) x - (1 + β * ξ t x) * delayedHeatForcing a p N t x) t := by
  obtain ⟨v, _, hd, heq⟩ := hξ.delayed_exists_time_derivative ha (ht.1.trans ht.2).le
  have hdt := (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hp : HasDerivAt (fun r ↦ ξ r x) (v t x) t := by
    simpa only [Function.comp_def, BUC.evalCLM_apply] using!
      (BUC.evalCLM (𝕜 := ℝ) (E := ℝ) x).hasFDerivAt.comp_hasDerivAt t hdt
  rwa [heq t ⟨ht.1.le, ht.2.le⟩] at hp

end

end Planarwave
