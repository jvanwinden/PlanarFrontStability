/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialRegularity
public import Planarwave.Analysis.HeatLinearRegularity

@[expose] public section

/-!
# All-order regularity for scalar-coefficient heat integral equations

The first-jet existence theorem is iterated, using the product rule and
spatial differentiation of Duhamel. This supplies the finite-order spatial
regularity part of the parabolic argument in Lemma `lem:xiAP`.
-/

open Set

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Duhamel continuity only needs source continuity on the finite horizon. -/
theorem continuousOn_heatDuhamel (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {f : ℝ → BUC E F} (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (heatDuhamel a f) (Icc 0 T) := by
  let f₀ := fun r : ℝ ↦ f (projIcc 0 T hT r)
  have hc : Continuous f₀ :=
    (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc
  apply (continuous_heatDuhamel a hc).continuousOn.congr
  intro t ht
  apply heatDuhamel_congr a ht.1
  intro r hr
  dsimp only [f₀]
  rw [projIcc_of_mem hT ⟨hr.1, hr.2.trans ht.2⟩]

/-- Differentiation under Duhamel on a finite horizon, including its endpoints. -/
theorem hasFDerivAt_heatDuhamel_on (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {f : ℝ → BUC E F} {f' : ℝ → BUC E (E →L[ℝ] F)}
    (hf : ContinuousOn f (Icc 0 T)) (hf' : ContinuousOn f' (Icc 0 T))
    (hd : ∀ r ∈ Icc 0 T, ∀ x, HasFDerivAt (f r) (f' r x) x)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    HasFDerivAt (heatDuhamel a f t) (heatDuhamel a f' t x) x := by
  let f₀ := fun r : ℝ ↦ f (projIcc 0 T hT r)
  let f₁ := fun r : ℝ ↦ f' (projIcc 0 T hT r)
  have hc₀ : Continuous f₀ :=
    (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc
  have hc₁ : Continuous f₁ :=
    (continuousOn_iff_continuous_domRestrict.mp hf').comp continuous_projIcc
  have h := hasFDerivAt_heatDuhamel a hc₀ hc₁
    (fun r y ↦ hd _ (projIcc 0 T hT r).property y) t x
  have he₀ : heatDuhamel a f₀ t = heatDuhamel a f t := by
    apply heatDuhamel_congr a ht.1
    intro r hr
    dsimp only [f₀]
    rw [projIcc_of_mem hT ⟨hr.1, hr.2.trans ht.2⟩]
  have he₁ : heatDuhamel a f₁ t = heatDuhamel a f' t := by
    apply heatDuhamel_congr a ht.1
    intro r hr
    dsimp only [f₁]
    rw [projIcc_of_mem hT ⟨hr.1, hr.2.trans ht.2⟩]
  simpa only [he₀, he₁] using! h

/-- Spatial BUC regularity propagates through the heat integral. -/
theorem BUCSpatialRegularOn.heatDuhamel (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {k : ℕ} {f : ℝ → BUC E F} (hf : BUCSpatialRegularOn (Icc 0 T) k f) :
    BUCSpatialRegularOn (Icc 0 T) k (heatDuhamel a f) := by
  induction k generalizing F with
  | zero => exact continuousOn_heatDuhamel a hT hf
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    exact ⟨continuousOn_heatDuhamel a hT hc, heatDuhamel a f', ih hf',
      fun _ ht x ↦ hasFDerivAt_heatDuhamel_on a hT hc hf'.continuous hd ht x⟩

/-- The finite-horizon version of Duhamel linearity for any Banach codomain. -/
theorem heatDuhamel_add_on (a : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {f g : ℝ → BUC E F} (hf : ContinuousOn f (Icc 0 t)) (hg : ContinuousOn g (Icc 0 t)) :
    heatDuhamel a (fun r ↦ f r + g r) t = heatDuhamel a f t + heatDuhamel a g t := by
  simp only [heatDuhamel, heatFlowBUC_add]
  apply intervalIntegral.integral_add
  · exact ((continuous_heatFlowBUC_joint a).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hf)).intervalIntegrable_of_Icc ht
  · exact ((continuous_heatFlowBUC_joint a).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hg)).intervalIntegrable_of_Icc ht

set_option maxHeartbeats 800000 in
/-- A scalar-coefficient heat integral equation preserves every finite order
of BUC spatial regularity. No derivative of the solution is assumed. -/
theorem bucSpatialRegularOn_scalar_heatVolterra (a : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (k : ℕ) (g : ℝ → BUC E ℝ) (f u : ℝ → BUC E F)
    (hg : BUCSpatialRegularOn (Icc 0 T) k g) (hf : BUCSpatialRegularOn (Icc 0 T) k f)
    (hu : ContinuousOn u (Icc 0 T))
    (heq : ∀ t ∈ Icc 0 T, u t = f t +
      heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (u r)) t) :
    BUCSpatialRegularOn (Icc 0 T) k u := by
  induction k generalizing F with
  | zero => exact hu
  | succ k ih =>
    have hgk := hg.of_succ
    have hfk := hf.of_succ
    have huk := ih f u hgk hfk hu heq
    obtain ⟨hgc, g', hg', hdg⟩ := hg
    obtain ⟨hfc, f', hf', hdf⟩ := hf
    obtain ⟨u', hu'c, hdu, hu'eq⟩ := exists_fderivative_scalar_heatVolterra a hT
      g g' f u f' hgc hg'.continuous hfc hf'.continuous hu hdg hdf heq
    let p := fun r ↦ BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E F) (g' r) (u r)
    have hp : BUCSpatialRegularOn (Icc 0 T) k p :=
      hg'.bilinear huk (ContinuousLinearMap.smulRightL ℝ E F)
    have hsource : BUCSpatialRegularOn (Icc 0 T) k (fun t ↦ f' t + heatDuhamel a p t) :=
      hf'.add (hp.heatDuhamel a hT)
    have heq' : ∀ t ∈ Icc 0 T, u' t = (f' t + heatDuhamel a p t) +
        heatDuhamel a (fun r ↦ BUC.smulBUC (g r) (u' r)) t := by
      intro t ht
      rw [hu'eq t ht, heatDuhamel_add_on a ht.1]
      · dsimp only [p]
        abel
      · exact ((BUC.continuous_bilinearBUC (ContinuousLinearMap.lsmul ℝ ℝ)).comp_continuousOn
          (hgc.prodMk hu'c.continuousOn)).mono (Icc_subset_Icc le_rfl ht.2)
      · exact hp.continuous.mono (Icc_subset_Icc le_rfl ht.2)
    exact ⟨hu, u', ih _ u' hgk hsource hu'c.continuousOn heq', hdu⟩

end

end Planarwave
