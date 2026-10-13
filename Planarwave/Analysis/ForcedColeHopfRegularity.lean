/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfExistence
public import Planarwave.Analysis.HeatDuhamelDerivative
public import Planarwave.Analysis.ScalarFirstJet
public import Planarwave.Analysis.DelayedHeatForcingDerivative

@[expose] public section

/-!
# First spatial regularity of the forced Cole--Hopf solution

For the regularity step in Lemma `lem:xiAP`, solve the linear equation in
the closed space of genuine first jets. Heat flow and multiplication by
the forcing preserve this space. Uniqueness identifies its value with
the previously constructed mild solution. Consequently the derivative
obtained here is genuine, not an assumed solution of a formal equation.
-/

open Set
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

-- Cache the standard instances for the nested jet-valued operator spaces.
local instance forcedColeHopfJetNormedAddCommGroup :
    NormedAddCommGroup (BUC E (FirstJet E ℝ)) := inferInstance
local instance forcedColeHopfJetNormedSpace :
    NormedSpace ℝ (BUC E (FirstJet E ℝ)) := inferInstance

/-- Solve the Cole--Hopf equation in the closed genuine-jet subspace. -/
theorem exists_forcedColeHopf_firstJet (a β : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (G : ℝ → BUC E (FirstJet E ℝ)) (hGc : Continuous G)
    (hG : ∀ r, G r ∈ firstJetSubmodule) :
    ∃ U : ℝ → BUC E (FirstJet E ℝ), Continuous U ∧
      (∀ r, U r ∈ firstJetSubmodule) ∧
      ∀ t ∈ Icc 0 T, U t = -heatDuhamel a
        (fun r ↦ G r + β • BUC.bilinearBUC scalarFirstJetMul (G r) (U r)) t := by
  let τ : NNReal := ⟨T, hT⟩
  let B : TimePath (E := BUC E (FirstJet E ℝ) →L[ℝ] BUC E (FirstJet E ℝ)) τ :=
    ⟨fun t ↦ (-β) • BUC.bilinearRightCLM scalarFirstJetMul (G t),
      (((BUC.bilinearBUCCLM (A := E) (scalarFirstJetMul (E := E))).continuous.comp hGc).const_smul (-β)).comp
        continuous_subtype_val⟩
  have hB : ∀ t u, u ∈ firstJetSubmodule → B t u ∈ firstJetSubmodule := by
    intro t u hu
    exact firstJetSubmodule.smul_mem (-β) (scalarFirstJetMul_mem_submodule (G t) u (hG t) hu)
  let f : TimePath (E := BUC E (FirstJet E ℝ)) τ :=
    ⟨fun t ↦ -heatDuhamel a G t,
      (continuous_heatDuhamel a hGc).neg.comp continuous_subtype_val⟩
  have hf : ∀ t, f t ∈ firstJetSubmodule := fun t ↦ firstJetSubmodule.neg_mem
    (heatDuhamel_mem_submodule a firstJetSubmodule isClosed_firstJetSubmodule
      (heatFlowBUC_mem_firstJetSubmodule a) hGc hG t)
  obtain ⟨u, hu, humem⟩ := exists_heatVolterraPath_mem_submodule a
    firstJetSubmodule isClosed_firstJetSubmodule (heatFlowBUC_mem_firstJetSubmodule a) B hB f hf
  let U := extendTimePath u
  have hUc : Continuous U := continuous_extendTimePath u
  have hprod : Continuous (fun r ↦ BUC.bilinearBUC scalarFirstJetMul (G r) (U r)) :=
    (BUC.continuous_bilinearBUC scalarFirstJetMul).comp (hGc.prodMk hUc)
  refine ⟨U, hUc, fun r ↦ humem _, ?_⟩
  intro t ht
  have hut := hu ⟨t, ht⟩
  have hclamp : heatVolterraPath a B u ⟨t, ht⟩ =
      heatDuhamel a (fun r ↦ (-β) • BUC.bilinearBUC scalarFirstJetMul (G r) (U r)) t := by
    apply heatDuhamel_congr a ht.1
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) (τ : ℝ) := ⟨hr.1, hr.2.trans ht.2⟩
    dsimp only
    rw [show extendTimePath B r = B ⟨r, hrT⟩ from extendTimePath_coe B ⟨r, hrT⟩]
    rfl
  rw [hclamp, heatDuhamel_smul, neg_smul] at hut
  have hc : Continuous (fun r ↦ β • BUC.bilinearBUC scalarFirstJetMul (G r) (U r)) :=
    hprod.const_smul β
  rw [heatDuhamel_add a hGc hc, heatDuhamel_smul]
  change U t = -(heatDuhamel a G t + _)
  rw [show U t = u ⟨t, ht⟩ from extendTimePath_coe u ⟨t, ht⟩, hut]
  change -heatDuhamel a G t + -(β • _) = _
  abel

/-- The mild solution has a genuine first spatial derivative continuous
in BUC, and that derivative satisfies the differentiated Duhamel formula.
Only one continuous BUC spatial derivative of the forcing is needed. -/
theorem IsForcedColeHopfMild.exists_buc_fderivative {a β T : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T) (hT : 0 ≤ T)
    (hg : ContinuousOn g (Icc 0 T)) (g' : ℝ → BUC E (E →L[ℝ] ℝ))
    (hg' : ContinuousOn g' (Icc 0 T))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (g t) (g' t x) x) :
    ∃ ξ' : ℝ → BUC E (E →L[ℝ] ℝ), Continuous ξ' ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (ξ' t x) x) ∧
      ∀ t ∈ Icc 0 T, ξ' t = -heatDuhamel a
        (fun r ↦ g' r + β • (BUC.smulBUC (g r) (ξ' r) + BUC.smulBUC (ξ r) (g' r))) t := by
  let τ : NNReal := ⟨T, hT⟩
  let gp : TimePath (E := BUC E ℝ) τ :=
    ⟨fun t ↦ g t, continuousOn_iff_continuous_domRestrict.mp hg⟩
  let dp : TimePath (E := BUC E (E →L[ℝ] ℝ)) τ :=
    ⟨fun t ↦ g' t, continuousOn_iff_continuous_domRestrict.mp hg'⟩
  let G := fun r ↦ firstJetBUC (extendTimePath gp r) (extendTimePath dp r)
  have hGc : Continuous G := continuous_firstJetBUC.comp
    ((continuous_extendTimePath gp).prodMk (continuous_extendTimePath dp))
  have hGmem : ∀ r, G r ∈ firstJetSubmodule := by
    intro r x
    simpa only [G, firstJetValue_firstJetBUC, firstJetDerivative_firstJetBUC] using!
      hderiv _ (Set.projIcc 0 (τ : ℝ) τ.2 r).property x
  have hGv : ∀ r ∈ Icc 0 T, firstJetValue (G r) = g r := by
    intro r hr
    exact (firstJetValue_firstJetBUC _ _).trans (extendTimePath_coe gp ⟨r, hr⟩)
  have hGd : ∀ r ∈ Icc 0 T, firstJetDerivative (G r) = g' r := by
    intro r hr
    exact (firstJetDerivative_firstJetBUC _ _).trans (extendTimePath_coe dp ⟨r, hr⟩)
  obtain ⟨U, hUc, hUm, hUeq⟩ := exists_forcedColeHopf_firstJet a β hT G hGc hGmem
  have hsource : Continuous
      (fun r ↦ G r + β • BUC.bilinearBUC scalarFirstJetMul (G r) (U r)) :=
    hGc.add (((BUC.continuous_bilinearBUC scalarFirstJetMul).comp (hGc.prodMk hUc)).const_smul β)
  have hv : IsForcedColeHopfMild a β g (fun r ↦ firstJetValue (U r)) T := by
    refine ⟨(firstJetValue.continuous.comp hUc).continuousOn, fun t ht ↦ ?_⟩
    rw [hUeq t ht, map_neg, firstJetValue_heatDuhamel a hsource]
    congr 1
    apply heatDuhamel_congr a ht.1
    intro r hr
    simp only [map_add, map_smul, firstJetValue_mul, forcedColeHopfSource]
    rw [hGv r ⟨hr.1, hr.2.trans ht.2⟩]
  have hident := hξ.unique hv hg hT
  refine ⟨fun r ↦ firstJetDerivative (U r), firstJetDerivative.continuous.comp hUc, ?_, ?_⟩
  · intro t ht x
    rw [hident ht]
    exact hUm t x
  · intro t ht
    dsimp only
    rw [hUeq t ht, map_neg, firstJetDerivative_heatDuhamel a hsource]
    congr 1
    apply heatDuhamel_congr a ht.1
    intro r hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    simp only [map_add, map_smul, firstJetDerivative_mul]
    rw [hGv r hrT, hGd r hrT, hident hrT]

/-- For the actual delayed forcing the regularity hypotheses above are
automatic: the completed source blocks need no spatial derivatives. -/
theorem IsForcedColeHopfMild.delayed_exists_buc_fderivative {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ ξ' : ℝ → BUC E (E →L[ℝ] ℝ), Continuous ξ' ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (ξ' t x) x) ∧
      ∀ t ∈ Icc 0 T, ξ' t = -heatDuhamel a
        (fun r ↦ delayedHeatForcingFDeriv ha p N r + β •
          (BUC.smulBUC (delayedHeatForcing a p N r) (ξ' r) +
            BUC.smulBUC (ξ r) (delayedHeatForcingFDeriv ha p N r))) t :=
  hξ.exists_buc_fderivative hT (continuous_delayedHeatForcing a p N).continuousOn
    (delayedHeatForcingFDeriv ha p N) (continuous_delayedHeatForcingFDeriv ha p N).continuousOn
    (fun t _ x ↦ hasFDerivAt_delayedHeatForcing ha p N t x)

/-- Existence of the actual delayed-forcing solution together with its
genuine, BUC-norm-continuous first spatial derivative. -/
theorem exists_delayed_forcedColeHopf_mild_fderivative {a : ℝ} (ha : 0 < a)
    (β : ℝ) {T : ℝ} (hT : 0 ≤ T) (p : BUC E ℝ) (N : ℝ → BUC E ℝ) :
    ∃ (ξ : ℝ → BUC E ℝ) (ξ' : ℝ → BUC E (E →L[ℝ] ℝ)),
      IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧ Continuous ξ' ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (ξ' t x) x) ∧
      ∀ t ∈ Icc 0 T, t ≤ 1 / 4 → ξ t = 0 ∧ ξ' t = 0 := by
  obtain ⟨ξ, hξ, hz⟩ := exists_delayed_forcedColeHopf_mild a β hT p N
  obtain ⟨ξ', hc, hd, _⟩ := hξ.delayed_exists_buc_fderivative ha hT
  refine ⟨ξ, ξ', hξ, hc, hd, fun t ht hq ↦ ⟨hz t ht hq, ?_⟩⟩
  ext x : 1
  have h := hd t ht x
  rw [hz t ht hq] at h
  simpa only [BUC.zero_apply] using
    h.unique (by simpa using! hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x)

end

end Planarwave
