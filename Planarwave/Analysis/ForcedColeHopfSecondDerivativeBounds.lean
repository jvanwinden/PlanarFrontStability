/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfSecondRegularity
public import Planarwave.Analysis.IntegrableDecayGronwall

@[expose] public section

/-!
# Uniform C² estimates for the forced Cole--Hopf solution

The twice differentiated Duhamel formula contains the four terms of
the second-order product rule. Heat contractivity bounds the maximum
of the value, derivative, and Hessian norms by one common integral.
Grönwall with the paper's integrable time weight then gives a uniform
bound, exactly as in the C^k argument of `lem:xiAP`.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

section Product

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Supremum bound for the tensor product in a spatial product rule. -/
theorem norm_bilinear_smulRightBUC_le (q : BUC E (E →L[ℝ] ℝ)) (v : BUC E F) :
    ‖BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E F) q v‖ ≤ ‖q‖ * ‖v‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  change ‖(q x).smulRight (v x)‖ ≤ _
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul (q.norm_apply_le x) (v.norm_apply_le x) (norm_nonneg (v x)) (norm_nonneg q)

end Product

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance c2BoundFirstBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance c2BoundFirstBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance c2BoundSecondTensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance c2BoundSecondTensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance c2BoundSecondBUCNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
local instance c2BoundSecondBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The first derivative source is bounded by the common C² majorant. -/
theorem norm_coleHopf_first_source_le {β R U : ℝ} (g ξ : BUC E ℝ)
    (g' q : BUC E (E →L[ℝ] ℝ)) (hg : ‖g‖ ≤ R) (hg' : ‖g'‖ ≤ R)
    (hξ : ‖ξ‖ ≤ U) (hq : ‖q‖ ≤ U) :
    ‖g' + β • (BUC.smulBUC g q + BUC.smulBUC ξ g')‖ ≤ R * (1 + (4 * |β|) * U) := by
  have hR := (norm_nonneg g).trans hg
  have hU := (norm_nonneg ξ).trans hξ
  have h1 : ‖BUC.smulBUC g q‖ ≤ R * U := (BUC.norm_smulBUC_le g q).trans (by gcongr)
  have h2 : ‖BUC.smulBUC ξ g'‖ ≤ R * U := (BUC.norm_smulBUC_le ξ g').trans
    (by calc
      _ ≤ U * R := by gcongr
      _ = _ := mul_comm _ _)
  calc
    _ ≤ ‖g'‖ + ‖β • (BUC.smulBUC g q + BUC.smulBUC ξ g')‖ := norm_add_le _ _
    _ ≤ R + |β| * (R * U + R * U) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hg' (mul_le_mul_of_nonneg_left (norm_add_le_of_le h1 h2) (abs_nonneg β))
    _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg β) (mul_nonneg hR hU)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Four product-rule terms control the actual second derivative source. -/
theorem norm_coleHopf_second_source_le {β R U : ℝ} (g ξ : BUC E ℝ)
    (g' q : BUC E (E →L[ℝ] ℝ)) (g'' h : BUC E (E →L[ℝ] E →L[ℝ] ℝ))
    (hg : ‖g‖ ≤ R) (hg' : ‖g'‖ ≤ R) (hg'' : ‖g''‖ ≤ R)
    (hξ : ‖ξ‖ ≤ U) (hq : ‖q‖ ≤ U) (hh : ‖h‖ ≤ U) :
    ‖g'' + β • (BUC.smulBUC g h + BUC.smulBUC ξ g'' +
      BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) q g' +
      BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) g' q)‖ ≤
      R * (1 + (4 * |β|) * U) := by
  have hR := (norm_nonneg g).trans hg
  have hU := (norm_nonneg ξ).trans hξ
  have h1 : ‖BUC.smulBUC g h‖ ≤ R * U := (BUC.norm_smulBUC_le g h).trans (by gcongr)
  have h2 : ‖BUC.smulBUC ξ g''‖ ≤ R * U := (BUC.norm_smulBUC_le ξ g'').trans
    (by calc
      _ ≤ U * R := by gcongr
      _ = _ := mul_comm _ _)
  have h3 : ‖BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) q g'‖ ≤ R * U :=
    (norm_bilinear_smulRightBUC_le q g').trans (by calc
      _ ≤ U * R := by gcongr
      _ = _ := mul_comm _ _)
  have h4 : ‖BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) g' q‖ ≤ R * U :=
    (norm_bilinear_smulRightBUC_le g' q).trans (by gcongr)
  calc
    _ ≤ ‖g''‖ + ‖β • (BUC.smulBUC g h + BUC.smulBUC ξ g'' +
      BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) q g' +
      BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) g' q)‖ := norm_add_le _ _
    _ ≤ R + |β| * (R * U + R * U + R * U + R * U) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hg'' (mul_le_mul_of_nonneg_left
        (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le h1 h2) h3) h4) (abs_nonneg β))
    _ = _ := by ring

/-- Integrate a common source majorant using only heat contractivity. -/
theorem norm_heatDuhamel_le_integral {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (a : ℝ) (f : ℝ → BUC E F)
    {t : ℝ} (ht : 0 ≤ t) {b : ℝ → ℝ} (hb : ContinuousOn b (Icc 0 t))
    (hbound : ∀ r ∈ Icc 0 t, ‖f r‖ ≤ b r) :
    ‖heatDuhamel a f t‖ ≤ ∫ r in (0 : ℝ)..t, b r := by
  apply intervalIntegral.norm_integral_le_of_norm_le ht
  · filter_upwards [] with r hr
    exact (norm_heatFlowBUC_le _ _ _).trans (hbound r ⟨hr.1.le, hr.2⟩)
  · exact hb.intervalIntegrable_of_Icc ht

/-- The uniform C² estimate, with genuine derivatives and a constant
independent of the final time. The product rule contributes the factor
four in Grönwall's coefficient. -/
theorem IsForcedColeHopfMild.exists_buc_second_fderivative_bound {a β T C M : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T)
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hg : Continuous g) (g' : ℝ → BUC E (E →L[ℝ] ℝ))
    (g'' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)) (hg' : Continuous g') (hg'' : Continuous g'')
    (hdg : ∀ t x, HasFDerivAt (g t) (g' t x) x) (hdg' : ∀ t x, HasFDerivAt (g' t) (g'' t x) x)
    (hdecay : ∀ t ∈ Icc 0 T, max ‖g t‖ (max ‖g' t‖ ‖g'' t‖) ≤
      C * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    ∃ (q : ℝ → BUC E (E →L[ℝ] ℝ)) (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      Continuous q ∧ Continuous h ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x) ∧
      ∀ t ∈ Icc 0 T, max ‖ξ t‖ (max ‖q t‖ ‖h t‖) ≤
        (4 * C * Real.exp (16 * |β| * C)) * M := by
  obtain ⟨q, h, hqc, hhc, hd, hqeq, hheq⟩ :=
    hξ.exists_buc_second_fderivative_duhamel hT hg g' g'' hg' hg'' hdg hdg'
  let ρ := fun r ↦ max ‖g r‖ (max ‖g' r‖ ‖g'' r‖)
  let u := fun r ↦ max ‖ξ r‖ (max ‖q r‖ ‖h r‖)
  have hρc : Continuous ρ := hg.norm.max (hg'.norm.max hg''.norm)
  have huc : ContinuousOn u (Icc 0 T) := fun t ht ↦
    (hξ.continuous.norm t ht).max (hqc.norm.max hhc.norm).continuousAt.continuousWithinAt
  have hρ0 : ∀ r, 0 ≤ ρ r := fun r ↦ (norm_nonneg (g r)).trans (le_max_left _ _)
  have hu0 : ∀ r, 0 ≤ u r := fun r ↦ (norm_nonneg (ξ r)).trans (le_max_left _ _)
  have hb : ContinuousOn (fun r ↦ ρ r * (1 + (4 * |β|) * u r)) (Icc 0 T) :=
    hρc.continuousOn.mul (continuousOn_const.add (huc.const_mul (4 * |β|)))
  have hi : ∀ t ∈ Icc 0 T, u t ≤ ∫ r in (0 : ℝ)..t, ρ r * (1 + (4 * |β|) * u r) := by
    intro t ht
    have hbt := hb.mono (Icc_subset_Icc le_rfl ht.2)
    apply max_le
    · rw [hξ.duhamel t ht, norm_neg]
      apply norm_heatDuhamel_le_integral a _ ht.1 hbt
      intro r _
      apply (norm_forcedColeHopfSource_le β (g r) (ξ r)).trans
      have hx : ‖ξ r‖ ≤ u r := le_max_left _ _
      have hs : 1 + |β| * ‖ξ r‖ ≤ 1 + (4 * |β|) * u r := by
        nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg β), mul_nonneg (abs_nonneg β) (hu0 r)]
      exact mul_le_mul (le_max_left _ _) hs (by positivity) (hρ0 r)
    · apply max_le
      · rw [hqeq t ht, norm_neg]
        apply norm_heatDuhamel_le_integral a _ ht.1 hbt
        intro r _
        exact norm_coleHopf_first_source_le (g r) (ξ r) (g' r) (q r)
          (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
          (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
      · rw [hheq t ht, norm_neg]
        apply norm_heatDuhamel_le_integral a _ ht.1 hbt
        intro r _
        exact norm_coleHopf_second_source_le (g r) (ξ r) (g' r) (q r) (g'' r) (h r)
          (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
          ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _)
          ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨q, h, hqc, hhc, hd, ?_⟩
  intro t ht
  have hbound := le_uniform_of_integral_decay hT (by positivity : 0 ≤ 4 * |β|) hC hM hM1
    huc hρc.continuousOn (fun r _ ↦ hρ0 r) hi hdecay ht
  convert hbound using 1
  congr 3
  ring

/-- The actual delayed forcing supplies both spatial derivatives without
derivative assumptions on its nonlinear source. -/
theorem IsForcedColeHopfMild.delayed_exists_buc_second_fderivative_bound {a β T C M : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hdecay : ∀ t ∈ Icc 0 T, max ‖delayedHeatForcing a p N t‖
      (max ‖delayedHeatForcingFDeriv ha p N t‖ ‖delayedHeatForcingFDeriv2 ha p N t‖) ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    ∃ (q : ℝ → BUC E (E →L[ℝ] ℝ)) (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      Continuous q ∧ Continuous h ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x) ∧
      ∀ t ∈ Icc 0 T, max ‖ξ t‖ (max ‖q t‖ ‖h t‖) ≤
        (4 * C * Real.exp (16 * |β| * C)) * M :=
  hξ.exists_buc_second_fderivative_bound hT hC hM hM1 (continuous_delayedHeatForcing a p N)
    (delayedHeatForcingFDeriv ha p N) (delayedHeatForcingFDeriv2 ha p N)
    (continuous_delayedHeatForcingFDeriv ha p N) (continuous_delayedHeatForcingFDeriv2 ha p N)
    (hasFDerivAt_delayedHeatForcing ha p N) (hasFDerivAt_delayedHeatForcingFDeriv ha p N) hdecay

end

end Planarwave
