/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamelDerivative
public import Planarwave.Analysis.VectorFirstJet

@[expose] public section

/-!
# Spatial regularity for scalar-coefficient vector heat equations

The first derivative of the Cole--Hopf variable solves an inhomogeneous
vector-valued heat Volterra equation. Solving that equation in the closed
first-jet subspace and using uniqueness proves another genuine derivative.
-/

open Set
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Uniqueness for global notation of the finite-horizon Volterra equation. -/
theorem heatVolterra_eqOn_unique (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (B : ℝ → BUC E F →L[ℝ] BUC E F) (hB : ContinuousOn B (Icc 0 T))
    (f u v : ℝ → BUC E F) (hf : ContinuousOn f (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (heu : ∀ t ∈ Icc 0 T, u t = f t + heatDuhamel a (fun r ↦ B r (u r)) t)
    (hev : ∀ t ∈ Icc 0 T, v t = f t + heatDuhamel a (fun r ↦ B r (v r)) t) :
    EqOn u v (Icc 0 T) := by
  let τ : NNReal := ⟨T, hT⟩
  let bp : TimePath (E := BUC E F →L[ℝ] BUC E F) τ :=
    ⟨fun t ↦ B t, continuousOn_iff_continuous_domRestrict.mp hB⟩
  let fp : TimePath (E := BUC E F) τ :=
    ⟨fun t ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf⟩
  let up : TimePath (E := BUC E F) τ :=
    ⟨fun t ↦ u t, continuousOn_iff_continuous_domRestrict.mp hu⟩
  let vp : TimePath (E := BUC E F) τ :=
    ⟨fun t ↦ v t, continuousOn_iff_continuous_domRestrict.mp hv⟩
  have hpath (w : ℝ → BUC E F) (hw : ContinuousOn w (Icc 0 T))
      (he : ∀ t ∈ Icc 0 T, w t = f t + heatDuhamel a (fun r ↦ B r (w r)) t) :
      let wp : TimePath (E := BUC E F) τ :=
        ⟨fun t ↦ w t, continuousOn_iff_continuous_domRestrict.mp hw⟩
      ∀ t, wp t = fp t + heatVolterraPath a bp wp t := by
    intro wp t
    change w t = f t + heatDuhamel a
      (fun r ↦ extendTimePath bp r (extendTimePath wp r)) t
    rw [he t t.2]
    congr 1
    apply heatDuhamel_congr a t.2.1
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) (τ : ℝ) := ⟨hr.1, hr.2.trans t.2.2⟩
    dsimp only
    rw [show extendTimePath bp r = bp ⟨r, hrT⟩ from extendTimePath_coe bp ⟨r, hrT⟩,
      show extendTimePath wp r = wp ⟨r, hrT⟩ from extendTimePath_coe wp ⟨r, hrT⟩]
    rfl
  obtain ⟨w, _, huniq⟩ := existsUnique_heatVolterraPath a bp fp
  have hp : up = vp := (huniq up (hpath u hu heu)).trans (huniq vp (hpath v hv hev)).symm
  intro t ht
  exact congrArg (fun q : TimePath (E := BUC E F) τ ↦ q ⟨t, ht⟩) hp

local instance heatLinearJetNormedAddCommGroup :
    NormedAddCommGroup (BUC E (FirstJet E F)) := inferInstance
local instance heatLinearJetNormedSpace : NormedSpace ℝ (BUC E (FirstJet E F)) := inferInstance

/-- One spatial derivative of the scalar coefficient and inhomogeneous
trajectory gives one genuine derivative of the vector-valued solution. -/
theorem exists_fderivative_scalar_heatVolterra (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (g : ℝ → BUC E ℝ) (g' : ℝ → BUC E (E →L[ℝ] ℝ))
    (f u : ℝ → BUC E F) (f' : ℝ → BUC E (E →L[ℝ] F))
    (hg : ContinuousOn g (Icc 0 T)) (hg' : ContinuousOn g' (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T)) (hf' : ContinuousOn f' (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T))
    (hdg : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (g t) (g' t x) x)
    (hdf : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (f t) (f' t x) x)
    (heq : ∀ t ∈ Icc 0 T, u t = f t + heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (u r)) t) :
    ∃ u' : ℝ → BUC E (E →L[ℝ] F), Continuous u' ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (u t) (u' t x) x) ∧
      ∀ t ∈ Icc 0 T, u' t = f' t + heatDuhamel a
        (fun r ↦ BUC.smulBUC (g r) (u' r) +
          BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E F) (g' r) (u r)) t := by
  let τ : NNReal := ⟨T, hT⟩
  let gp : TimePath (E := BUC E (FirstJet E ℝ)) τ :=
    ⟨fun t ↦ firstJetBUC (g t) (g' t), continuousOn_iff_continuous_domRestrict.mp
      (continuous_firstJetBUC.comp_continuousOn (hg.prodMk hg'))⟩
  let fp : TimePath (E := BUC E (FirstJet E F)) τ :=
    ⟨fun t ↦ firstJetBUC (f t) (f' t), continuousOn_iff_continuous_domRestrict.mp
      (continuous_firstJetBUC.comp_continuousOn (hf.prodMk hf'))⟩
  have hgp : ∀ t, gp t ∈ firstJetSubmodule := by
    intro t x
    change HasFDerivAt (firstJetValue (firstJetBUC (g t) (g' t)))
      (firstJetDerivative (firstJetBUC (g t) (g' t)) x) x
    simpa only [firstJetValue_firstJetBUC, firstJetDerivative_firstJetBUC] using hdg t t.2 x
  have hfp : ∀ t, fp t ∈ firstJetSubmodule := by
    intro t x
    change HasFDerivAt (firstJetValue (firstJetBUC (f t) (f' t)))
      (firstJetDerivative (firstJetBUC (f t) (f' t)) x) x
    simpa only [firstJetValue_firstJetBUC, firstJetDerivative_firstJetBUC] using hdf t t.2 x
  let B : TimePath (E := BUC E (FirstJet E F) →L[ℝ] BUC E (FirstJet E F)) τ :=
    ⟨fun t ↦ BUC.bilinearRightCLM (firstJetSMul (E := E) (F := F)) (gp t),
      (BUC.bilinearBUCCLM (A := E) (firstJetSMul (E := E) (F := F))).continuous.comp gp.continuous⟩
  have hB : ∀ t v, v ∈ firstJetSubmodule → B t v ∈ firstJetSubmodule :=
    fun t v hv ↦ firstJetSMul_mem_submodule (gp t) v (hgp t) hv
  obtain ⟨U, hUeq, hUm⟩ := exists_heatVolterraPath_mem_submodule a
    firstJetSubmodule isClosed_firstJetSubmodule (heatFlowBUC_mem_firstJetSubmodule a) B hB fp hfp
  let J := extendTimePath U
  let G := extendTimePath gp
  have hJc : Continuous J := continuous_extendTimePath U
  have hprod : Continuous (fun r ↦ BUC.bilinearBUC (firstJetSMul (E := E) (F := F)) (G r) (J r)) := by
    change Continuous (fun r ↦ extendTimePath B r (J r))
    exact (continuous_extendTimePath B).clm_apply hJc
  have hGeq (r : ℝ) (hr : r ∈ Icc 0 T) : G r = firstJetBUC (g r) (g' r) :=
    extendTimePath_coe gp ⟨r, hr⟩
  have hJeq (t : ℝ) (ht : t ∈ Icc 0 T) :
      J t = firstJetBUC (f t) (f' t) + heatDuhamel a
        (fun r ↦ BUC.bilinearBUC (firstJetSMul (E := E) (F := F)) (G r) (J r)) t := by
    rw [show J t = U ⟨t, ht⟩ from extendTimePath_coe U ⟨t, ht⟩, hUeq]
    rfl
  have hv : ∀ t ∈ Icc 0 T, firstJetValue (J t) = f t +
      heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (firstJetValue (J r))) t := by
    intro t ht
    rw [hJeq t ht, map_add, firstJetValue_firstJetBUC, firstJetValue_heatDuhamel a hprod]
    congr 1
    apply heatDuhamel_congr a ht.1
    intro r hr
    dsimp only
    simp only [firstJetValue_smul, hGeq r ⟨hr.1, hr.2.trans ht.2⟩, firstJetValue_firstJetBUC]
  have hident := heatVolterra_eqOn_unique a hT
    (fun r ↦ BUC.bilinearRightCLM (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) (g r))
    ((BUC.bilinearBUCCLM (A := E) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)).continuous.comp_continuousOn hg)
    f u (fun r ↦ firstJetValue (J r)) hf hu (firstJetValue.continuous.comp hJc).continuousOn heq hv
  refine ⟨fun r ↦ firstJetDerivative (J r), firstJetDerivative.continuous.comp hJc, ?_, ?_⟩
  · intro t ht x
    rw [hident ht]
    exact hUm _ x
  · intro t ht
    dsimp only
    rw [hJeq t ht, map_add, firstJetDerivative_firstJetBUC, firstJetDerivative_heatDuhamel a hprod]
    congr 1
    apply heatDuhamel_congr a ht.1
    intro r hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    dsimp only
    simp only [firstJetDerivative_smul, hGeq r hrT, firstJetValue_firstJetBUC,
      firstJetDerivative_firstJetBUC]
    rw [hident hrT]

end

end Planarwave
