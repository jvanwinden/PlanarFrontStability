/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.InverseModulationNonlinearity
public import Planarwave.Analysis.BUCNonlinearHigher

@[expose] public section

/-!
# Norm continuity of the inverse-modulation remainder

The delayed phase and forcing vanish initially. Consequently the nonlinear
source there is just the reaction remainder, which is continuous for rough
BUC perturbations and does not require initial spatial derivatives.
-/

open Set Filter

noncomputable section

namespace BUC

variable {A E F : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The reaction remainder depends continuously on the perturbation in BUC norm. -/
theorem continuous_reactionRemainder (f : E → F) (hf : ContDiff ℝ 2 f)
    (p : BUC A E) : Continuous (reactionRemainder f hf p) := by
  exact (((continuous_postcompContinuous f (hf.of_le (by norm_num))).comp
    (continuous_const.add continuous_id)).sub continuous_const).sub
      (operatorApplyCLM (postcompContinuous (fderiv ℝ f)
        (hf.continuous_fderiv (by norm_num)) p)).continuous

/-- Continuous scalar and vector fields have a continuous pointwise product. -/
theorem continuousOn_smulBUC {I : Set ℝ} {b : ℝ → BUC A ℝ} {w : ℝ → BUC A F}
    (hb : ContinuousOn b I) (hw : ContinuousOn w I) :
    ContinuousOn (fun t ↦ smulBUC (b t) (w t)) I := by
  change ContinuousOn (fun t ↦ bilinearBUC
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) (b t) (w t)) I
  simpa only [bilinearBUCCLM_apply] using!
    (((bilinearBUCCLM (A := A)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)).continuous.comp_continuousOn hb).clm_apply hw)

omit [ProperSpace E] in
/-- Joint continuity for pointwise application of operator-valued BUC fields. -/
theorem continuousOn_operatorApply {I : Set ℝ} {b : ℝ → BUC A (E →L[ℝ] F)}
    {w : ℝ → BUC A E} (hb : ContinuousOn b I) (hw : ContinuousOn w I) :
    ContinuousOn (fun t ↦ operatorApply (b t) (w t)) I := by
  change ContinuousOn (fun t ↦ bilinearBUC ((ContinuousLinearMap.apply ℝ F :
    E →L[ℝ] (E →L[ℝ] F) →L[ℝ] F).flip) (b t) (w t)) I
  simpa only [bilinearBUCCLM_apply] using!
    (((bilinearBUCCLM (A := A) ((ContinuousLinearMap.apply ℝ F :
      E →L[ℝ] (E →L[ℝ] F) →L[ℝ] F).flip)).continuous.comp_continuousOn hb).clm_apply hw)

end BUC

namespace Planarwave

variable {Y F : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]

local instance : NormedAddCommGroup (BUC (Y × ℝ) (Y →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := Y →L[ℝ] F)
local instance : NormedAddCommGroup (BUC (Y × ℝ) F) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := F)
local instance : NormedAddCommGroup (BUC (Y × ℝ) Y) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := Y)
local instance : NormedAddCommGroup (BUC (Y × ℝ) ℝ) :=
  BUC.instNormedAddCommGroup (α := Y × ℝ) (E := ℝ)
local instance : NormedAddCommGroup (BUC Y Y) :=
  BUC.instNormedAddCommGroup (α := Y) (E := Y)
local instance : NormedAddCommGroup (BUC Y ℝ) :=
  BUC.instNormedAddCommGroup (α := Y) (E := ℝ)

omit [InnerProductSpace ℝ Y] in
/-- Transverse pullback preserves continuity of time-dependent BUC fields. -/
theorem continuousOn_transverseLift {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {I : Set ℝ} {w : ℝ → BUC Y G} (hw : ContinuousOn w I) :
    ContinuousOn (fun t ↦ transverseLift (w t)) I :=
  (BUC.compCLM (𝕜 := ℝ) Prod.fst uniformContinuous_fst).continuous.comp_continuousOn hw

/-- The squared gradient norm is continuous as a scalar BUC field. -/
theorem continuousOn_phaseGradientSquared {I : Set ℝ} {s : ℝ → BUC Y Y}
    (hs : ContinuousOn s I) : ContinuousOn (fun t ↦ phaseGradientSquared (s t)) I :=
  (BUC.continuous_bilinearBUC (innerSL ℝ)).comp_continuousOn (hs.prodMk hs)

/-- All derivative-dependent terms vanish when the phase derivatives and forcing vanish. -/
theorem inverseModulationNonlinearity_zero_phase (f : F → F) (hf : ContDiff ℝ 2 f)
    (D : F →L[ℝ] F) (c a : ℝ) (p v vz vzz : BUC (Y × ℝ) F)
    (vyz : BUC (Y × ℝ) (Y →L[ℝ] F)) :
    inverseModulationNonlinearity f hf D c a p v vz vzz vyz 0 0 0 =
      BUC.reactionRemainder f hf p v := by
  ext x
  simp [inverseModulationNonlinearity_apply, BUC.reactionRemainder_apply]

/-- On positive-time slabs, continuity follows termwise from bounded bilinear operations. -/
theorem continuousOn_inverseModulationNonlinearity {I : Set ℝ}
    (f : F → F) (hf : ContDiff ℝ 2 f) (D : F →L[ℝ] F) (c a : ℝ)
    (p : BUC (Y × ℝ) F) {v vz vzz : ℝ → BUC (Y × ℝ) F}
    {vyz : ℝ → BUC (Y × ℝ) (Y →L[ℝ] F)}
    {s : ℝ → BUC Y Y} {l g : ℝ → BUC Y ℝ}
    (hv : ContinuousOn v I) (hvz : ContinuousOn vz I) (hvzz : ContinuousOn vzz I)
    (hvyz : ContinuousOn vyz I) (hs : ContinuousOn s I)
    (hl : ContinuousOn l I) (hg : ContinuousOn g I) :
    ContinuousOn (fun t ↦ inverseModulationNonlinearity f hf D c a p
      (v t) (vz t) (vzz t) (vyz t) (s t) (l t) (g t)) I := by
  have hsq : ContinuousOn (fun t ↦ phaseGradientSquared (s t)) I :=
    continuousOn_phaseGradientSquared hs
  have happ : ContinuousOn (fun t ↦ BUC.operatorApply (vyz t) (transverseLift (s t))) I :=
    BUC.continuousOn_operatorApply hvyz (continuousOn_transverseLift hs)
  have hR : ContinuousOn (fun t ↦ BUC.reactionRemainder f hf p (v t)) I :=
    (BUC.continuous_reactionRemainder f hf p).comp_continuousOn hv
  have hL : ContinuousOn (fun t ↦ BUC.smulBUC (transverseLift (l t))
      (a • vz t - BUC.postcompCLM D (vz t))) I :=
    BUC.continuousOn_smulBUC (continuousOn_transverseLift hl) ((hvz.const_smul a).sub
      ((BUC.postcompCLM D).continuous.comp_continuousOn hvz))
  have hS : ContinuousOn (fun t ↦ BUC.smulBUC (transverseLift (phaseGradientSquared (s t)))
      (BUC.postcompCLM D (vzz t) + (c / 2) • vz t)) I :=
    BUC.continuousOn_smulBUC (continuousOn_transverseLift hsq) (((BUC.postcompCLM D).continuous.comp_continuousOn hvzz).add
      (hvz.const_smul (c / 2)))
  have hM : ContinuousOn (fun t ↦ (2 : ℝ) • BUC.postcompCLM D
      (BUC.operatorApply (vyz t) (transverseLift (s t)))) I :=
    ((BUC.postcompCLM D).continuous.comp_continuousOn happ).const_smul (2 : ℝ)
  have hG : ContinuousOn (fun t ↦ BUC.smulBUC (transverseLift (g t)) (vz t)) I :=
    BUC.continuousOn_smulBUC (continuousOn_transverseLift hg) hvz
  exact (((hR.add hL).add hS).sub hM).sub hG

/-- Initial vanishing of the phase coefficients removes any need for the spatial
jets to converge at zero. Only the perturbation itself must be continuous there. -/
theorem continuousOn_inverseModulationNonlinearity_of_initial_zero
    (f : F → F) (hf : ContDiff ℝ 2 f) (D : F →L[ℝ] F) (c a : ℝ)
    (p : BUC (Y × ℝ) F) {T δ : ℝ} (hδ : 0 < δ)
    {v vz vzz : ℝ → BUC (Y × ℝ) F} {vyz : ℝ → BUC (Y × ℝ) (Y →L[ℝ] F)}
    {s : ℝ → BUC Y Y} {l g : ℝ → BUC Y ℝ}
    (hv : ContinuousOn v (Icc 0 T))
    (hvz : ContinuousOn vz (Ioc 0 T)) (hvzz : ContinuousOn vzz (Ioc 0 T))
    (hvyz : ContinuousOn vyz (Ioc 0 T))
    (hs : ContinuousOn s (Ioc 0 T)) (hl : ContinuousOn l (Ioc 0 T))
    (hg : ContinuousOn g (Ioc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < δ → s t = 0 ∧ l t = 0 ∧ g t = 0) :
    ContinuousOn (fun t ↦ inverseModulationNonlinearity f hf D c a p
      (v t) (vz t) (vzz t) (vyz t) (s t) (l t) (g t)) (Icc 0 T) := by
  let N := fun t ↦ inverseModulationNonlinearity f hf D c a p
    (v t) (vz t) (vzz t) (vyz t) (s t) (l t) (g t)
  have hN : ContinuousOn N (Ioc 0 T) :=
    continuousOn_inverseModulationNonlinearity f hf D c a p
      (hv.mono Ioc_subset_Icc_self) hvz hvzz hvyz hs hl hg
  have hnear : ∀ t ∈ Icc 0 T, t < δ → N t = BUC.reactionRemainder f hf p (v t) := by
    intro t ht htδ
    obtain ⟨hs0, hl0, hg0⟩ := hzero t ht htδ
    dsimp [N]
    rw [hs0, hl0, hg0, inverseModulationNonlinearity_zero_phase]
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    apply (((BUC.continuous_reactionRemainder f hf p).comp_continuousOn hv) 0 ht).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr hrδ
      exact hnear r hr hrδ
    · exact hnear 0 ht hδ
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    exact (hN t ⟨hpos, ht.2⟩).mono_of_mem_nhdsWithin
      (by filter_upwards [self_mem_nhdsWithin,
            (eventually_gt_nhds hpos).filter_mono nhdsWithin_le_nhds] with r hr hr0
          exact ⟨hr0, hr.2⟩)

end Planarwave
