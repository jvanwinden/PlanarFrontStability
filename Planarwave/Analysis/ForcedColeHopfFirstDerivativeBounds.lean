/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfRegularity
public import Planarwave.Analysis.HeatDuhamelBilinearBounds

@[expose] public section

/-!
# Uniform C¹ bounds for the forced Cole--Hopf solution

Apply the paper's heat-contractivity/product-rule/Grönwall argument in
the closed space of genuine first derivative jets. The estimate is
independent of the time horizon; the derivative being bounded is
constructed, not supplied as a solution of a formal derivative equation.
-/

open Set
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

section JetNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_firstJetValue_le (u : BUC E (FirstJet E F)) : ‖firstJetValue u‖ ≤ ‖u‖ := by
  apply (BUC.norm_le (norm_nonneg u)).mpr
  intro x
  exact (norm_fst_le (u x)).trans (u.norm_apply_le x)

theorem norm_firstJetDerivative_le (u : BUC E (FirstJet E F)) : ‖firstJetDerivative u‖ ≤ ‖u‖ := by
  apply (BUC.norm_le (norm_nonneg u)).mpr
  intro x
  exact (norm_snd_le (u x)).trans (u.norm_apply_le x)

/-- The jet norm is the usual maximum of the zeroth and first BUC norms. -/
theorem norm_firstJetBUC (f : BUC E F) (q : BUC E (E →L[ℝ] F)) :
    ‖firstJetBUC f q‖ = max ‖f‖ ‖q‖ := by
  apply le_antisymm
  · apply (BUC.norm_le ((norm_nonneg f).trans (le_max_left _ _))).mpr
    intro x
    simp only [firstJetBUC_apply, Prod.norm_def]
    exact max_le_max (f.norm_apply_le x) (q.norm_apply_le x)
  · apply max_le
    · simpa only [firstJetValue_firstJetBUC] using norm_firstJetValue_le (firstJetBUC f q)
    · simpa only [firstJetDerivative_firstJetBUC] using norm_firstJetDerivative_le (firstJetBUC f q)

local instance boundedScalarFirstJetNormedAddCommGroup :
    NormedAddCommGroup (FirstJet E ℝ) := inferInstance
local instance boundedScalarFirstJetNormedSpace :
    NormedSpace ℝ (FirstJet E ℝ) := inferInstance

/-- The first-order product rule costs at most a factor of two. -/
theorem norm_scalarFirstJetMul_le : ‖scalarFirstJetMul (E := E)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  exact norm_scalarFirstJetMulRight_apply_le p q

end JetNorm

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance boundedColeHopfJetNormedAddCommGroup :
    NormedAddCommGroup (BUC E (FirstJet E ℝ)) := inferInstance
local instance boundedColeHopfJetNormedSpace :
    NormedSpace ℝ (BUC E (FirstJet E ℝ)) := inferInstance

/-- The C¹ version of the a priori estimate in `lem:xiAP`, including
existence of the genuine first derivative. Its constant depends only on
the forcing constant and `β`, and not on `T`, `M`, or the solution. -/
theorem IsForcedColeHopfMild.exists_buc_fderivative_bound {a β T C M : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T)
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hg : ContinuousOn g (Icc 0 T)) (g' : ℝ → BUC E (E →L[ℝ] ℝ))
    (hg' : ContinuousOn g' (Icc 0 T))
    (hdg : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (g t) (g' t x) x)
    (hdecay : ∀ t ∈ Icc 0 T, max ‖g t‖ ‖g' t‖ ≤ C * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    ∃ q : ℝ → BUC E (E →L[ℝ] ℝ), Continuous q ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x) ∧
      ∀ t ∈ Icc 0 T, max ‖ξ t‖ ‖q t‖ ≤ (4 * C * Real.exp (8 * |β| * C)) * M := by
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
      hdg _ (Set.projIcc 0 (τ : ℝ) τ.2 r).property x
  have hGeq : ∀ t ∈ Icc 0 T, G t = firstJetBUC (g t) (g' t) := by
    intro t ht
    dsimp only [G]
    rw [show extendTimePath gp t = g t from extendTimePath_coe gp ⟨t, ht⟩,
      show extendTimePath dp t = g' t from extendTimePath_coe dp ⟨t, ht⟩]
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
    simp only [map_add, map_smul, firstJetValue_mul, forcedColeHopfSource,
      hGeq r ⟨hr.1, hr.2.trans ht.2⟩, firstJetValue_firstJetBUC]
  have hident := hξ.unique hv hg hT
  have hbound : ∀ t ∈ Icc 0 T, ‖U t‖ ≤ (4 * C * Real.exp (8 * |β| * C)) * M := by
    intro t ht
    have h := norm_le_decay_of_bilinear_heatDuhamel scalarFirstJetMul (by norm_num : (0 : ℝ) ≤ 2)
      norm_scalarFirstJetMul_le hGc.continuousOn hUc.continuousOn hT hC hM hM1 hUeq
      (fun r hr ↦ by simpa only [hGeq r hr, norm_firstJetBUC] using hdecay r hr) ht
    convert h using 1
    congr 3
    ring
  refine ⟨fun r ↦ firstJetDerivative (U r), firstJetDerivative.continuous.comp hUc, ?_, ?_⟩
  · intro t ht x
    rw [hident ht]
    exact hUm t x
  · intro t ht
    rw [hident ht]
    exact max_le ((norm_firstJetValue_le (U t)).trans (hbound t ht))
      ((norm_firstJetDerivative_le (U t)).trans (hbound t ht))

/-- Apply the C¹ estimate to the actual derivative of delayed forcing;
no derivative assumptions on the completed nonlinear source are needed. -/
theorem IsForcedColeHopfMild.delayed_exists_buc_fderivative_bound {a β T C M : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hdecay : ∀ t ∈ Icc 0 T,
      max ‖delayedHeatForcing a p N t‖ ‖delayedHeatForcingFDeriv ha p N t‖ ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    ∃ q : ℝ → BUC E (E →L[ℝ] ℝ), Continuous q ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x) ∧
      ∀ t ∈ Icc 0 T, max ‖ξ t‖ ‖q t‖ ≤ (4 * C * Real.exp (8 * |β| * C)) * M :=
  hξ.exists_buc_fderivative_bound hT hC hM hM1 (continuous_delayedHeatForcing a p N).continuousOn
    (delayedHeatForcingFDeriv ha p N) (continuous_delayedHeatForcingFDeriv ha p N).continuousOn
    (fun t _ x ↦ hasFDerivAt_delayedHeatForcing ha p N t x) hdecay

end

end Planarwave
