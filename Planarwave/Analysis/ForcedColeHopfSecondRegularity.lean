/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfRegularity
public import Planarwave.Analysis.HeatLinearRegularity
public import Planarwave.Analysis.DelayedHeatForcingSecondDerivative

@[expose] public section

/-!
# Second spatial regularity of the forced Cole--Hopf solution

Differentiate the vector-valued equation for the first derivative using
the scalar-coefficient heat regularity theorem. The inhomogeneous term
uses only the already constructed first derivative and two derivatives
of the forcing. This is the next parabolic-regularity step in `lem:xiAP`.
-/

open Set
open scoped Laplacian
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance coleHopfFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] ℝ)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] ℝ)
local instance coleHopfFirstDerivativeNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] ℝ)) :=
  BUC.instNormedSpace (𝕜 := ℝ) (α := E) (E := E →L[ℝ] ℝ)
local instance coleHopfSecondTensorNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coleHopfSecondTensorNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

local instance coleHopfSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] E →L[ℝ] ℝ)
local instance coleHopfSecondDerivativeNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] ℝ)) :=
  BUC.instNormedSpace (𝕜 := ℝ) (α := E) (E := E →L[ℝ] E →L[ℝ] ℝ)

set_option maxHeartbeats 400000 in
/-- Two BUC derivatives of the forcing give two genuine BUC spatial
derivatives of the existing mild solution, both continuous in time. -/
theorem IsForcedColeHopfMild.exists_buc_second_fderivative_duhamel {a β T : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T) (hT : 0 ≤ T)
    (hg : Continuous g) (g' : ℝ → BUC E (E →L[ℝ] ℝ))
    (g'' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ))
    (hg' : Continuous g') (hg'' : Continuous g'')
    (hdg : ∀ t x, HasFDerivAt (g t) (g' t x) x)
    (hdg' : ∀ t x, HasFDerivAt (g' t) (g'' t x) x) :
    ∃ (ξ' : ℝ → BUC E (E →L[ℝ] ℝ)) (ξ'' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      Continuous ξ' ∧ Continuous ξ'' ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (ξ' t x) x ∧
        HasFDerivAt (ξ' t) (ξ'' t x) x) ∧
      (∀ t ∈ Icc 0 T, ξ' t = -heatDuhamel a
        (fun r ↦ g' r + β • (BUC.smulBUC (g r) (ξ' r) + BUC.smulBUC (ξ r) (g' r))) t) ∧
      ∀ t ∈ Icc 0 T, ξ'' t = -heatDuhamel a
        (fun r ↦ g'' r + β • (BUC.smulBUC (g r) (ξ'' r) + BUC.smulBUC (ξ r) (g'' r) +
          BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (ξ' r) (g' r) +
          BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (g' r) (ξ' r))) t := by
  obtain ⟨q, hqc, hqd, hqeq⟩ := hξ.exists_buc_fderivative hT hg.continuousOn g' hg'.continuousOn
    (fun t _ x ↦ hdg t x)
  let τ : NNReal := ⟨T, hT⟩
  let xp : TimePath (E := BUC E ℝ) τ :=
    ⟨fun t ↦ ξ t, continuousOn_iff_continuous_domRestrict.mp hξ.continuous⟩
  let qp : TimePath (E := BUC E (E →L[ℝ] ℝ)) τ :=
    ⟨fun t ↦ q t, hqc.comp continuous_subtype_val⟩
  let X := extendTimePath xp
  let Q := extendTimePath qp
  have hXc : Continuous X := continuous_extendTimePath xp
  have hQc : Continuous Q := continuous_extendTimePath qp
  have hXd : ∀ t x, HasFDerivAt (X t) (Q t x) x := fun t x ↦
    hqd _ (Set.projIcc 0 (τ : ℝ) τ.2 t).property x
  have hXeq : ∀ t ∈ Icc 0 T, X t = ξ t := fun t ht ↦ extendTimePath_coe xp ⟨t, ht⟩
  let P := fun r ↦ g' r + β • BUC.smulBUC (X r) (g' r)
  let P' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ) := fun r ↦ g'' r + β •
    (BUC.smulBUC (X r) (g'' r) +
      BUC.bilinearBUC (𝕜 := ℝ) (G := E →L[ℝ] E →L[ℝ] ℝ)
        (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (Q r) (g' r))
  let B₁ : BUC E ℝ →L[ℝ] BUC E (E →L[ℝ] ℝ) →L[ℝ] BUC E (E →L[ℝ] ℝ) :=
    BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)
  let B₂ : BUC E ℝ →L[ℝ] BUC E (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
      BUC E (E →L[ℝ] E →L[ℝ] ℝ) := BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)
  let B₃ : BUC E (E →L[ℝ] ℝ) →L[ℝ] BUC E (E →L[ℝ] ℝ) →L[ℝ]
      BUC E (E →L[ℝ] E →L[ℝ] ℝ) :=
    BUC.bilinearBUCCLM (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ))
  have hPc : Continuous P := hg'.add (((B₁.continuous.comp hXc).clm_apply hg').const_smul β)
  have hP'c : Continuous P' := hg''.add
    ((((B₂.continuous.comp hXc).clm_apply hg'').add
      ((B₃.continuous.comp hQc).clm_apply hg')).const_smul β)
  have hPd : ∀ r x, HasFDerivAt (P r) (P' r x) x := by
    intro r x
    simpa only [P, P', BUC.add_apply, BUC.smul_apply, BUC.smulBUC_apply,
      BUC.bilinearBUC_apply, ContinuousLinearMap.smulRightL_apply_apply] using!
      (hdg' r x).add (((hXd r x).smul (hdg' r x)).const_smul β)
  let f := fun t ↦ -heatDuhamel a P t
  let f' := fun t ↦ -heatDuhamel a P' t
  have hfc : Continuous f := (continuous_heatDuhamel a hPc).neg
  have hf'c : Continuous f' := (continuous_heatDuhamel a hP'c).neg
  have hfd : ∀ t x, HasFDerivAt (f t) (f' t x) x := by
    intro t x
    simpa only [f, f', BUC.neg_apply] using! (hasFDerivAt_heatDuhamel a hPc hP'c hPd t x).neg
  have hqg : Continuous (fun r ↦ BUC.smulBUC (g r) (q r)) :=
    (B₁.continuous.comp hg).clm_apply hqc
  have heq : ∀ t ∈ Icc 0 T, q t = f t +
      heatDuhamel a (fun r ↦ BUC.smulBUC ((-β) • g r) (q r)) t := by
    intro t ht
    have hs : heatDuhamel a
        (fun r ↦ g' r + β • (BUC.smulBUC (g r) (q r) + BUC.smulBUC (ξ r) (g' r))) t =
        heatDuhamel a (fun r ↦ P r + β • BUC.smulBUC (g r) (q r)) t := by
      apply heatDuhamel_congr a ht.1
      intro r hr
      dsimp only [P]
      rw [hXeq r ⟨hr.1, hr.2.trans ht.2⟩, smul_add]
      abel
    have hb : (fun r ↦ BUC.smulBUC ((-β) • g r) (q r)) =
        fun r ↦ (-β) • BUC.smulBUC (g r) (q r) := by
      funext r
      ext x v
      simp [smul_smul]
    have hβq : Continuous (fun r ↦ β • BUC.smulBUC (g r) (q r)) := hqg.const_smul β
    rw [hqeq t ht, hs, heatDuhamel_add a hPc hβq, heatDuhamel_smul, hb, heatDuhamel_smul]
    dsimp only [f]
    rw [neg_smul]
    abel
  obtain ⟨q', hq'c, hq'd, hq'eq⟩ := exists_fderivative_scalar_heatVolterra a hT
    (fun r ↦ (-β) • g r) (fun r ↦ (-β) • g' r) f q f'
    (hg.const_smul (-β)).continuousOn (hg'.const_smul (-β)).continuousOn
    hfc.continuousOn hf'c.continuousOn hqc.continuousOn
    (fun t _ x ↦ by simpa only [BUC.smul_apply] using! (hdg t x).const_smul (-β))
    (fun t _ x ↦ hfd t x) heq
  refine ⟨q, q', hqc, hq'c, fun t ht x ↦ ⟨hqd t ht x, hq'd t ht x⟩, hqeq, ?_⟩
  let R := fun r ↦ BUC.smulBUC ((-β) • g r) (q' r) +
    BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) ((-β) • g' r) (q r)
  have hRc : Continuous R := by
    let B : BUC E ℝ →L[ℝ] BUC E (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
        BUC E (E →L[ℝ] E →L[ℝ] ℝ) := BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    let C : BUC E (E →L[ℝ] ℝ) →L[ℝ] BUC E (E →L[ℝ] ℝ) →L[ℝ]
        BUC E (E →L[ℝ] E →L[ℝ] ℝ) :=
      BUC.bilinearBUCCLM (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ))
    exact ((B.continuous.comp (hg.const_smul (-β))).clm_apply hq'c).add
      ((C.continuous.comp (hg'.const_smul (-β))).clm_apply hqc)
  intro t ht
  rw [hq'eq t ht]
  change -heatDuhamel a P' t + heatDuhamel a R t = _
  have hneg : heatDuhamel a (fun r ↦ -P' r) t = -heatDuhamel a P' t := by
    simpa only [neg_one_smul] using heatDuhamel_smul a (-1) P' t
  rw [← hneg, ← heatDuhamel_add a (f := fun r ↦ -P' r) (g := R) hP'c.neg hRc]
  have hnegall (F : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)) :
      heatDuhamel a (fun r ↦ -F r) t = -heatDuhamel a F t := by
    simpa only [neg_one_smul] using heatDuhamel_smul a (-1) F t
  rw [← hnegall]
  apply heatDuhamel_congr a ht.1
  intro r hr
  have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
  have hQeq : Q r = q r := extendTimePath_coe qp ⟨r, hrT⟩
  dsimp only [P', R]
  rw [hXeq r hrT, hQeq]
  ext x v w
  simp [smul_smul, smul_add]
  ring

/-- Two genuine BUC derivatives, as a projection of the differentiated
Duhamel construction. -/
theorem IsForcedColeHopfMild.exists_buc_second_fderivative {a β T : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T) (hT : 0 ≤ T)
    (hg : Continuous g) (g' : ℝ → BUC E (E →L[ℝ] ℝ))
    (g'' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ))
    (hg' : Continuous g') (hg'' : Continuous g'')
    (hdg : ∀ t x, HasFDerivAt (g t) (g' t x) x)
    (hdg' : ∀ t x, HasFDerivAt (g' t) (g'' t x) x) :
    ∃ (ξ' : ℝ → BUC E (E →L[ℝ] ℝ)) (ξ'' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      Continuous ξ' ∧ Continuous ξ'' ∧
      ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (ξ' t x) x ∧
        HasFDerivAt (ξ' t) (ξ'' t x) x := by
  obtain ⟨q, h, hqc, hhc, hd, _, _⟩ :=
    hξ.exists_buc_second_fderivative_duhamel hT hg g' g'' hg' hg'' hdg hdg'
  exact ⟨q, h, hqc, hhc, hd⟩

/-- The delayed-forcing mild solution has two spatial BUC derivatives,
without any derivative assumptions on its completed nonlinear source. -/
theorem IsForcedColeHopfMild.delayed_exists_buc_second_fderivative {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ (ξ' : ℝ → BUC E (E →L[ℝ] ℝ)) (ξ'' : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      Continuous ξ' ∧ Continuous ξ'' ∧
      ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (ξ' t x) x ∧
        HasFDerivAt (ξ' t) (ξ'' t x) x :=
  hξ.exists_buc_second_fderivative hT (continuous_delayedHeatForcing a p N)
    (delayedHeatForcingFDeriv ha p N) (delayedHeatForcingFDeriv2 ha p N)
    (continuous_delayedHeatForcingFDeriv ha p N) (continuous_delayedHeatForcingFDeriv2 ha p N)
    (hasFDerivAt_delayedHeatForcing ha p N) (hasFDerivAt_delayedHeatForcingFDeriv ha p N)

/-- In particular each spatial slice of the delayed mild solution is
twice continuously differentiable, including at the initial time. -/
theorem IsForcedColeHopfMild.delayed_contDiff_two {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ 2 (ξ t : E → ℝ) := by
  obtain ⟨q, h, _, _, hd⟩ := hξ.delayed_exists_buc_second_fderivative ha hT
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨q t, ?_, fun x ↦ (hd t ht x).1⟩
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨h t, (h t).continuous, fun x ↦ (hd t ht x).2⟩

/-- The Laplacian is an actual BUC field continuous in time. This is the
spatial prerequisite for identifying the classical heat equation. -/
theorem IsForcedColeHopfMild.delayed_exists_buc_laplacian {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ L : ℝ → BUC E ℝ, Continuous L ∧
      ∀ t ∈ Icc 0 T, ∀ x, L t x = Δ (ξ t : E → ℝ) x := by
  obtain ⟨q, h, _, hc, hd⟩ := hξ.delayed_exists_buc_second_fderivative ha hT
  let traceMap : BUC E (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] BUC E ℝ :=
    BUC.postcompCLM (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ) (F := ℝ)
      (laplacianTraceCLM (E := E) (F := ℝ))
  refine ⟨fun t ↦ traceMap (h t), traceMap.continuous.comp hc, ?_⟩
  intro t ht x
  exact (laplacian_eq_trace_of_hasFDerivAt (ξ t) (q t) (h t)
    (fun y ↦ (hd t ht y).1) (fun y ↦ (hd t ht y).2) x).symm

/-- Construct the delayed-forcing solution and its first two genuine BUC
derivatives. All three vanish during the initial inactive forcing interval. -/
theorem exists_delayed_forcedColeHopf_mild_second_fderivative {a : ℝ} (ha : 0 < a)
    (β : ℝ) {T : ℝ} (hT : 0 ≤ T) (p : BUC E ℝ) (N : ℝ → BUC E ℝ) :
    ∃ (ξ : ℝ → BUC E ℝ) (q : ℝ → BUC E (E →L[ℝ] ℝ))
      (h : ℝ → BUC E (E →L[ℝ] E →L[ℝ] ℝ)),
      IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧
      Continuous q ∧ Continuous h ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x ∧ HasFDerivAt (q t) (h t x) x) ∧
      ∀ t ∈ Icc 0 T, t ≤ 1 / 4 → ξ t = 0 ∧ q t = 0 ∧ h t = 0 := by
  obtain ⟨ξ, hξ, hz⟩ := exists_delayed_forcedColeHopf_mild a β hT p N
  obtain ⟨q, h, hqc, hhc, hd⟩ := hξ.delayed_exists_buc_second_fderivative ha hT
  refine ⟨ξ, q, h, hξ, hqc, hhc, hd, ?_⟩
  intro t ht hquarter
  have hqzero : q t = 0 := by
    ext x : 1
    have hq := (hd t ht x).1
    rw [hz t ht hquarter] at hq
    simpa only [BUC.zero_apply] using
      hq.unique (by simpa using! hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x)
  refine ⟨hz t ht hquarter, hqzero, ?_⟩
  ext x : 1
  have hh := (hd t ht x).2
  rw [hqzero] at hh
  simpa only [BUC.zero_apply] using
    hh.unique (by simpa using! hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x)

end

end Planarwave
