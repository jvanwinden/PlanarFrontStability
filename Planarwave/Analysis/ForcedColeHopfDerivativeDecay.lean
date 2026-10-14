/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfSecondDerivativeBounds
public import Planarwave.Analysis.HeatDerivativeDecay

@[expose] public section

/-!
# Weighted derivative decay for the forced Cole--Hopf solution

This is the derivative-decay part of Step 1 of `lem:key`, namely
`eq:xiestC1C2`. First use the uniform C² estimate to bound the source
`g(1+βξ)` and its first two derivatives. Heat smoothing and the `5/4`
convolution estimate then give the half- and full-power decay rates.
-/

open Set

namespace Planarwave

noncomputable section

/-- Constant in the already proved uniform C² estimate. -/
def coleHopfC2BoundConstant (β C : ℝ) : ℝ := 4 * C * Real.exp (16 * |β| * C)

/-- Common bound for the value and first two derivatives of `g(1+βξ)`. -/
def coleHopfC2SourceConstant (β C : ℝ) : ℝ :=
  C * (1 + (4 * |β|) * coleHopfC2BoundConstant β C)

theorem coleHopfC2BoundConstant_nonneg (β : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ coleHopfC2BoundConstant β C := by unfold coleHopfC2BoundConstant; positivity

theorem coleHopfC2SourceConstant_nonneg (β : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ coleHopfC2SourceConstant β C := by
  have h := coleHopfC2BoundConstant_nonneg β hC
  unfold coleHopfC2SourceConstant
  positivity

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance coleDecayFirstBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance coleDecayFirstBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance coleDecaySecondTensorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coleDecaySecondTensorNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coleDecaySecondBUCNormedAddCommGroup : NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance
local instance coleDecaySecondBUCNormedSpace : NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) := inferInstance

/-- Actual first and second derivatives of the mild solution satisfy
the paper's weighted decay, with constants independent of the horizon. -/
theorem IsForcedColeHopfMild.exists_buc_second_fderivative_decay {a β T C M : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hg : Continuous g) (g' : ℝ → BUC E (E →L[ℝ] ℝ))
    (g'' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)) (hg' : Continuous g') (hg'' : Continuous g'')
    (hdg : ∀ t x, HasFDerivAt (g t) (g' t x) x) (hdg' : ∀ t x, HasFDerivAt (g' t) (g'' t x) x)
    (hdecay : ∀ t ∈ Icc 0 T, max ‖g t‖ (max ‖g' t‖ ‖g'' t‖) ≤
      C * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    ∃ (q : ℝ → BUC E (E →L[ℝ] ℝ)) (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      Continuous q ∧ Continuous h ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x) ∧
      ∀ t ∈ Icc 0 T,
        max ‖ξ t‖ (max ‖q t‖ ‖h t‖) ≤ coleHopfC2BoundConstant β C * M ∧
        ‖q t‖ ≤ (16 * max 1 (Real.sqrt (2 * a))⁻¹) * coleHopfC2SourceConstant β C * M *
          (1 + t) ^ (-(1 / 2 : ℝ)) ∧
        ‖h t‖ ≤ (32 * max 1 a⁻¹) * coleHopfC2SourceConstant β C * M *
          (1 + t) ^ (-(1 : ℝ)) := by
  obtain ⟨q, h, hqc, hhc, hd, hqeq, hheq⟩ :=
    hξ.exists_buc_second_fderivative_duhamel hT hg g' g'' hg' hg'' hdg hdg'
  obtain ⟨Q, H, _, _, hD, hB⟩ :=
    hξ.exists_buc_second_fderivative_bound hT hC hM hM1 hg g' g'' hg' hg'' hdg hdg' hdecay
  have hqQ : ∀ r ∈ Icc 0 T, q r = Q r := by
    intro r hr
    ext x : 1
    exact (hd r hr x).1.unique (hD r hr x).1
  have hhH : ∀ r ∈ Icc 0 T, h r = H r := by
    intro r hr
    ext x : 1
    have hx := (hd r hr x).2
    rw [hqQ r hr] at hx
    exact hx.unique (hD r hr x).2
  have hb : ∀ r ∈ Icc 0 T, max ‖ξ r‖ (max ‖q r‖ ‖h r‖) ≤ coleHopfC2BoundConstant β C * M := by
    intro r hr
    rw [hqQ r hr, hhH r hr]
    exact hB r hr
  let F := fun r ↦ forcedColeHopfSource β (g r) (ξ r)
  let F' := fun r ↦ g' r + β • (BUC.smulBUC (g r) (q r) + BUC.smulBUC (ξ r) (g' r))
  let F'' := fun r ↦ g'' r + β • (BUC.smulBUC (g r) (h r) + BUC.smulBUC (ξ r) (g'' r) +
    BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (q r) (g' r) +
    BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (g' r) (q r))
  have hdF : ∀ r ∈ Icc 0 T, ∀ x, HasFDerivAt (F r) (F' r x) x := by
    intro r hr x
    simpa only [F, F', forcedColeHopfSource, BUC.add_apply, BUC.smul_apply,
      BUC.smulBUC_apply, smul_eq_mul] using!
      (hdg r x).add (((hdg r x).mul (hd r hr x).1).const_smul β)
  have hdF' : ∀ r ∈ Icc 0 T, ∀ x, HasFDerivAt (F' r) (F'' r x) x := by
    intro r hr x
    simpa only [F', F'', BUC.add_apply, BUC.smul_apply, BUC.smulBUC_apply,
      BUC.bilinearBUC_apply, ContinuousLinearMap.smulRightL_apply_apply,
      add_assoc, add_left_comm, add_comm] using!
      (hdg' r x).add ((((hdg r x).smul (hd r hr x).2).add
        (((hd r hr x).1).smul (hdg' r x))).const_smul β)
  have hsource : ∀ r ∈ Icc 0 T, max ‖F r‖ (max ‖F' r‖ ‖F'' r‖) ≤
      (coleHopfC2SourceConstant β C * M) * (1 + r) ^ (-(5 : ℝ) / 4) := by
    intro r hr
    let R := C * M * (1 + r) ^ (-(5 : ℝ) / 4)
    let U := coleHopfC2BoundConstant β C
    have hU : 0 ≤ U := coleHopfC2BoundConstant_nonneg β hC
    have hu : max ‖ξ r‖ (max ‖q r‖ ‖h r‖) ≤ U :=
      (hb r hr).trans ((mul_le_mul_of_nonneg_left hM1 hU).trans_eq (mul_one U))
    have hx : ‖ξ r‖ ≤ U := (le_max_left _ _).trans hu
    have hq : ‖q r‖ ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans hu)
    have hh : ‖h r‖ ≤ U := (le_max_right _ _).trans ((le_max_right _ _).trans hu)
    have hg0 : ‖g r‖ ≤ R := (le_max_left _ _).trans (hdecay r hr)
    have hg1 : ‖g' r‖ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans (hdecay r hr))
    have hg2 : ‖g'' r‖ ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans (hdecay r hr))
    have hR : 0 ≤ R := (norm_nonneg (g r)).trans hg0
    have hF : ‖F r‖ ≤ R * (1 + (4 * |β|) * U) := by
      apply (norm_forcedColeHopfSource_le β (g r) (ξ r)).trans
      apply mul_le_mul hg0 _ (by positivity) hR
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg β), mul_nonneg (abs_nonneg β) hU]
    have hF' := norm_coleHopf_first_source_le (β := β) (g r) (ξ r) (g' r) (q r) hg0 hg1 hx hq
    have hF'' := norm_coleHopf_second_source_le (β := β) (g r) (ξ r) (g' r) (q r) (g'' r) (h r)
      hg0 hg1 hg2 hx hq hh
    apply (max_le hF (max_le hF' hF'')).trans_eq
    dsimp only [R, U, coleHopfC2SourceConstant]
    ring
  refine ⟨q, h, hqc, hhc, hd, fun t ht ↦ ⟨hb t ht, ?_, ?_⟩⟩
  · rw [hqeq t ht, norm_neg]
    change ‖heatDuhamel a F' t‖ ≤ _
    have hsub : ∀ r ∈ Icc 0 t, r ∈ Icc 0 T := fun r hr ↦ ⟨hr.1, hr.2.trans ht.2⟩
    have hi := norm_heatDuhamel_fderivative_decay_le ha ht.1
      (mul_nonneg (coleHopfC2SourceConstant_nonneg β hC) hM) F F'
      (fun r hr ↦ hdF r (hsub r hr))
      (fun r hr ↦ (le_max_left _ _).trans (hsource r (hsub r hr)))
      (fun r hr ↦ (le_max_left _ _).trans ((le_max_right _ _).trans (hsource r (hsub r hr))))
    simpa only [mul_assoc] using hi
  · rw [hheq t ht, norm_neg]
    change ‖heatDuhamel a F'' t‖ ≤ _
    have hsub : ∀ r ∈ Icc 0 t, r ∈ Icc 0 T := fun r hr ↦ ⟨hr.1, hr.2.trans ht.2⟩
    have hi := norm_heatDuhamel_second_fderivative_decay_le ha ht.1
      (mul_nonneg (coleHopfC2SourceConstant_nonneg β hC) hM) F F' F''
      (fun r hr ↦ hdF r (hsub r hr)) (fun r hr ↦ hdF' r (hsub r hr))
      (fun r hr ↦ (le_max_left _ _).trans (hsource r (hsub r hr)))
      (fun r hr ↦ (le_max_right _ _).trans ((le_max_right _ _).trans (hsource r (hsub r hr))))
    simpa only [mul_assoc] using hi

/-- The delayed forcing supplies the derivative hypotheses automatically. -/
theorem IsForcedColeHopfMild.delayed_exists_buc_second_fderivative_decay {a β T C M : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hdecay : ∀ t ∈ Icc 0 T, max ‖delayedHeatForcing a p N t‖
      (max ‖delayedHeatForcingFDeriv ha p N t‖ ‖delayedHeatForcingFDeriv2 ha p N t‖) ≤
        C * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    ∃ (q : ℝ → BUC E (E →L[ℝ] ℝ)) (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      Continuous q ∧ Continuous h ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x) ∧
      ∀ t ∈ Icc 0 T,
        max ‖ξ t‖ (max ‖q t‖ ‖h t‖) ≤ coleHopfC2BoundConstant β C * M ∧
        ‖q t‖ ≤ (16 * max 1 (Real.sqrt (2 * a))⁻¹) * coleHopfC2SourceConstant β C * M *
          (1 + t) ^ (-(1 / 2 : ℝ)) ∧
        ‖h t‖ ≤ (32 * max 1 a⁻¹) * coleHopfC2SourceConstant β C * M *
          (1 + t) ^ (-(1 : ℝ)) :=
  hξ.exists_buc_second_fderivative_decay ha hT hC hM hM1 (continuous_delayedHeatForcing a p N)
    (delayedHeatForcingFDeriv ha p N) (delayedHeatForcingFDeriv2 ha p N)
    (continuous_delayedHeatForcingFDeriv ha p N) (continuous_delayedHeatForcingFDeriv2 ha p N)
    (hasFDerivAt_delayedHeatForcing ha p N) (hasFDerivAt_delayedHeatForcingFDeriv ha p N) hdecay

end

end Planarwave
