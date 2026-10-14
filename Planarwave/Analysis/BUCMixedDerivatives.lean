/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCFirstJet
public import Planarwave.Analysis.HeatVolterraInvariant
public import Planarwave.Analysis.BUCSpacetimeCalculus

@[expose] public section

/-!
# Commuting time and space derivatives of BUC trajectories

Integrate in the closed graph of the spatial derivative, then apply the
fundamental theorem of calculus in BUC norm. This proves existence of
the time derivative of the spatial derivative, without presupposing
mixed differentiability. It is the commutation input for higher joint
spacetime regularity after parabolic smoothing.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Planarwave

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance mixedDerivativeFieldNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance mixedDerivativeFieldNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance mixedDerivativeBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup
local instance mixedDerivativeBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] F)) :=
  BUC.instNormedSpace

/-- Spatial differentiation commutes with a BUC-valued time integral:
the genuine first-derivative graph is closed under integration. -/
theorem hasFDerivAt_buc_intervalIntegral {f : ℝ → BUC E F}
    {q : ℝ → BUC E (E →L[ℝ] F)} (hf : Continuous f) (hq : Continuous q)
    (hd : ∀ r x, HasFDerivAt (f r) (q r x) x) (a b : ℝ) (x : E) :
    HasFDerivAt ((∫ r in a..b, f r : BUC E F) : E → F) ((∫ r in a..b, q r) x) x := by
  let j := fun r ↦ firstJetBUC (f r) (q r)
  have hj : Continuous j := continuous_firstJetBUC.comp (hf.prodMk hq)
  have hmem : ∀ r, j r ∈ firstJetSubmodule := by
    intro r y
    simpa only [j, firstJetValue_firstJetBUC, firstJetDerivative_firstJetBUC] using hd r y
  have hi := closedSubmodule_intervalIntegral_mem firstJetSubmodule isClosed_firstJetSubmodule
    hj hmem a b
  have hval : firstJetValue (∫ r in a..b, j r) = ∫ r in a..b, f r := by
    rw [← firstJetValue.intervalIntegral_comp_comm (hj.intervalIntegrable _ _)]
    simp only [j, firstJetValue_firstJetBUC]
  have hder : firstJetDerivative (∫ r in a..b, j r) = ∫ r in a..b, q r := by
    rw [← firstJetDerivative.intervalIntegral_comp_comm (hj.intervalIntegrable _ _)]
    simp only [j, firstJetDerivative_firstJetBUC]
  simpa only [hval, hder] using hi x

/-- The integral commutation only requires continuity and derivative
identities on the actual integration interval. -/
theorem hasFDerivAt_buc_intervalIntegral_on {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → BUC E F} {q : ℝ → BUC E (E →L[ℝ] F)}
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hd : ∀ r ∈ Icc a b, ∀ x, HasFDerivAt (f r) (q r x) x) (x : E) :
    HasFDerivAt ((∫ r in a..b, f r : BUC E F) : E → F) ((∫ r in a..b, q r) x) x := by
  let f₀ := fun r ↦ f (projIcc a b hab r)
  let q₀ := fun r ↦ q (projIcc a b hab r)
  have hf₀ : Continuous f₀ := (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc
  have hq₀ : Continuous q₀ := (continuousOn_iff_continuous_domRestrict.mp hq).comp continuous_projIcc
  have hd₀ := hasFDerivAt_buc_intervalIntegral hf₀ hq₀
    (fun r y ↦ hd _ (projIcc a b hab r).property y) a b x
  have heqf : (∫ r in a..b, f₀ r) = ∫ r in a..b, f r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hab] at hr
    dsimp only [f₀]
    rw [projIcc_of_mem hab hr]
  have heqq : (∫ r in a..b, q₀ r) = ∫ r in a..b, q r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hab] at hr
    dsimp only [q₀]
    rw [projIcc_of_mem hab hr]
  simpa only [heqf, heqq] using! hd₀

omit [NormedSpace ℝ E] in
/-- On a finite interval, continuous pointwise time derivatives integrate
to the corresponding identity in the BUC norm. -/
theorem buc_intervalIntegral_eq_sub_of_pointwise {a b : ℝ} (hab : a ≤ b)
    {u v : ℝ → BUC E F} (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (htime : ∀ r ∈ Ioo a b, ∀ x, HasDerivAt (fun t ↦ u t x) (v r x) r) :
    (∫ r in a..b, v r) = u b - u a := by
  apply BUC.ext
  intro x
  change (BUC.evalCLM (𝕜 := ℝ) x) (∫ r in a..b, v r) = u b x - u a x
  rw [← (BUC.evalCLM (𝕜 := ℝ) x).intervalIntegral_comp_comm (hv.intervalIntegrable_of_Icc hab)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    ((BUC.evalCLM (𝕜 := ℝ) x).continuous.comp_continuousOn hu)
    (fun r hr ↦ htime r hr x)
    (((BUC.evalCLM (𝕜 := ℝ) x).continuous.comp_continuousOn hv).intervalIntegrable_of_Icc hab)

/-- The time derivative of the spatial derivative is the spatial
derivative of the time derivative. The conclusion is in the BUC norm;
the mixed derivative is derived, not assumed. -/
theorem hasDerivAt_buc_spatial_derivative {a b : ℝ}
    {u v : ℝ → BUC E F} {q qv : ℝ → BUC E (E →L[ℝ] F)}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hqv : ContinuousOn qv (Icc a b))
    (htime : ∀ r ∈ Ioo a b, ∀ x, HasDerivAt (fun t ↦ u t x) (v r x) r)
    (hspace : ∀ r ∈ Icc a b, ∀ x, HasFDerivAt (u r) (q r x) x)
    (hvspace : ∀ r ∈ Icc a b, ∀ x, HasFDerivAt (v r) (qv r x) x)
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt q (qv t) t := by
  have hab : a ≤ b := (ht.1.trans ht.2).le
  have heq (s : ℝ) (hs : s ∈ Icc a b) : (∫ r in a..s, qv r) = q s - q a := by
    have hvsub := hv.mono (Icc_subset_Icc le_rfl hs.2)
    have hqvsub := hqv.mono (Icc_subset_Icc le_rfl hs.2)
    have hint := buc_intervalIntegral_eq_sub_of_pointwise hs.1
      (hu.mono (Icc_subset_Icc le_rfl hs.2)) hvsub
      (fun r hr x ↦ htime r ⟨hr.1, hr.2.trans_le hs.2⟩ x)
    apply BUC.ext
    intro x
    have hd := hasFDerivAt_buc_intervalIntegral_on hs.1 hvsub hqvsub
      (fun r hr y ↦ hvspace r ⟨hr.1, hr.2.trans hs.2⟩ y) x
    rw [hint] at hd
    exact hd.unique ((hspace s hs x).sub (hspace a ⟨le_rfl, hab⟩ x))
  have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hi := intervalIntegral.integral_hasDerivAt_right
    ((hqv.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hqv.mono Ioo_subset_Icc_self) t ht)
    (hqv.continuousAt hnhds)
  apply (hi.add_const (q a)).congr_of_eventuallyEq
  filter_upwards [hnhds] with s hs
  rw [heq s hs, sub_add_cancel]

end

end Planarwave
