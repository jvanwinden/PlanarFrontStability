/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatVolterra
public import Planarwave.Analysis.ForcedColeHopfPhase
public import Planarwave.Analysis.DelayedHeatForcingRegularity

@[expose] public section

/-!
# Existence of the forced Cole--Hopf mild solution

The coefficient is the actual multiplication map `-β g(t)` and the
inhomogeneous term is the heat Duhamel response to `-g`. The Volterra
construction produces a continuous BUC-valued solution on every finite
interval. Restriction and uniqueness give consistency and causality.

Together with the previously proved Grönwall bounds this establishes
existence of the small continuous modulation phase. Classical regularity
and the higher-order estimates in Lemma `lem:xiAP` remain separate steps.
-/

open Set
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The forced Cole--Hopf equation has a continuous BUC-valued mild
solution on every finite time interval. No smallness assumption is used. -/
theorem exists_forcedColeHopf_mild (a β : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (g : ℝ → BUC E ℝ) (hg : ContinuousOn g (Icc 0 T)) :
    ∃ ξ : ℝ → BUC E ℝ, IsForcedColeHopfMild a β g ξ T := by
  let τ : NNReal := ⟨T, hT⟩
  let gp : TimePath (E := BUC E ℝ) τ :=
    ⟨fun t ↦ g t, continuousOn_iff_continuous_domRestrict.mp hg⟩
  let G := extendTimePath gp
  have hGc : Continuous G := continuous_extendTimePath gp
  have hGeq : ∀ r ∈ Icc 0 T, G r = g r := by
    intro r hr
    exact extendTimePath_coe gp ⟨r, hr⟩
  let B : TimePath (E := BUC E ℝ →L[ℝ] BUC E ℝ) τ :=
    ⟨fun t ↦ (-β) • BUC.bilinearRightCLM (ContinuousLinearMap.lsmul ℝ ℝ) (gp t),
      ((BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp
        gp.continuous).const_smul (-β)⟩
  let f : TimePath (E := BUC E ℝ) τ :=
    ⟨fun t ↦ -heatDuhamel a G t,
      ((continuous_heatDuhamel a hGc).neg).comp continuous_subtype_val⟩
  obtain ⟨u, hu, _⟩ := existsUnique_heatVolterraPath a B f
  let ξ := extendTimePath u
  have hξc : Continuous ξ := continuous_extendTimePath u
  have hprod : Continuous (fun r ↦ BUC.smulBUC (G r) (ξ r)) :=
    (BUC.continuous_bilinearBUC (ContinuousLinearMap.lsmul ℝ ℝ)).comp (hGc.prodMk hξc)
  refine ⟨ξ, hξc.continuousOn, ?_⟩
  intro t ht
  have hut := hu ⟨t, ht⟩
  have hext : ξ t = u ⟨t, ht⟩ := extendTimePath_coe u ⟨t, ht⟩
  change u ⟨t, ht⟩ = -heatDuhamel a G t +
    heatDuhamel a (fun r ↦ (-β) • BUC.smulBUC (G r) (ξ r)) t at hut
  rw [heatDuhamel_smul, neg_smul] at hut
  have hsplit : heatDuhamel a (fun r ↦ forcedColeHopfSource β (G r) (ξ r)) t =
      heatDuhamel a G t + β • heatDuhamel a (fun r ↦ BUC.smulBUC (G r) (ξ r)) t := by
    unfold forcedColeHopfSource
    have hc : Continuous (fun r ↦ β • BUC.smulBUC (G r) (ξ r)) := hprod.const_smul β
    rw [heatDuhamel_add a hGc hc, heatDuhamel_smul]
  have hsource : heatDuhamel a (fun r ↦ forcedColeHopfSource β (G r) (ξ r)) t =
      heatDuhamel a (fun r ↦ forcedColeHopfSource β (g r) (ξ r)) t := by
    apply heatDuhamel_congr a ht.1
    intro r hr
    dsimp only
    rw [hGeq r ⟨hr.1, hr.2.trans ht.2⟩]
  rw [hext, hut, ← hsource, hsplit]
  abel

/-- Restricting the final time preserves the mild equation. -/
theorem IsForcedColeHopfMild.mono {a β S T : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hST : S ≤ T) :
    IsForcedColeHopfMild a β g ξ S :=
  ⟨hξ.continuous.mono (Icc_subset_Icc le_rfl hST),
    fun t ht ↦ hξ.duhamel t ⟨ht.1, ht.2.trans hST⟩⟩

/-- The equation on `[0,T]` only uses forcing values on that interval. -/
theorem IsForcedColeHopfMild.congr_forcing {a β T : ℝ} {g h ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hgh : EqOn g h (Icc 0 T)) :
    IsForcedColeHopfMild a β h ξ T := by
  refine ⟨hξ.continuous, fun t ht ↦ ?_⟩
  rw [hξ.duhamel t ht]
  congr 1
  apply heatDuhamel_congr a ht.1
  intro r hr
  dsimp only
  rw [hgh ⟨hr.1, hr.2.trans ht.2⟩]

/-- Causality: solutions with equal past forcing have equal past values,
regardless of their later forcing or final times. -/
theorem IsForcedColeHopfMild.eqOn_of_forcing_eqOn {a β S T U : ℝ}
    {g h ξ η : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ S) (hη : IsForcedColeHopfMild a β h η T)
    (hU : 0 ≤ U) (hUS : U ≤ S) (hUT : U ≤ T)
    (hg : ContinuousOn g (Icc 0 U)) (hgh : EqOn g h (Icc 0 U)) :
    EqOn ξ η (Icc 0 U) :=
  (hξ.mono hUS).unique ((hη.mono hUT).congr_forcing hgh.symm) hg hU

/-- Restart the mild solution at an intermediate time. This is the local
evolution formula used when extending the tracking scheme. -/
theorem IsForcedColeHopfMild.restart {a β T s t : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (ha : 0 ≤ a)
    (hg : ContinuousOn g (Icc 0 T)) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ξ t = heatFlowBUC a (t - s) (ξ s) -
      ∫ r in s..t, heatFlowBUC a (t - r) (forcedColeHopfSource β (g r) (ξ r)) := by
  have hc : ContinuousOn (fun r ↦ forcedColeHopfSource β (g r) (ξ r)) (Icc 0 t) :=
    ((continuous_forcedColeHopfSource β).comp_continuousOn
      (hg.prodMk hξ.continuous)).mono (Icc_subset_Icc le_rfl ht)
  rw [hξ.duhamel t ⟨hs.trans hst, ht⟩, hξ.duhamel s ⟨hs, hst.trans ht⟩]
  change -heatDuhamel a _ t =
    (heatOperator a (t - s)) (-heatDuhamel a _ s) - _
  rw [map_neg, heatOperator_apply, heatDuhamel_restart ha hs hst _ hc]
  abel

/-- Zero forcing has the identically zero mild solution. -/
theorem isForcedColeHopfMild_zero (a β T : ℝ) :
    IsForcedColeHopfMild a β (fun _ ↦ (0 : BUC E ℝ)) (fun _ ↦ 0) T := by
  refine ⟨continuousOn_const, fun t _ ↦ ?_⟩
  have hsource : forcedColeHopfSource β (0 : BUC E ℝ) 0 = 0 := by ext x; simp
  have hheat : ∀ s, heatFlowBUC a s (0 : BUC E ℝ) = 0 :=
    fun s ↦ (heatOperator a s).map_zero
  simp [hsource, heatDuhamel, hheat]

/-- A zero initial forcing interval gives a zero solution interval. -/
theorem IsForcedColeHopfMild.eq_zero_of_forcing_eq_zero {a β S T : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T)
    (hS : 0 ≤ S) (hST : S ≤ T) (hg : EqOn g (fun _ ↦ 0) (Icc 0 S)) :
    EqOn ξ (fun _ ↦ 0) (Icc 0 S) :=
  ((hξ.mono hST).congr_forcing hg).unique (isForcedColeHopfMild_zero a β S)
    continuousOn_const hS

/-- In particular the delayed tracking forcing leaves the Cole--Hopf
variable identically zero through time `1/4`. -/
theorem IsForcedColeHopfMild.delayed_initial_zero {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (hquarter : t ≤ 1 / 4) : ξ t = 0 :=
  hξ.eq_zero_of_forcing_eq_zero ht.1 ht.2
    (fun _r hr ↦ delayedHeatForcing_eq_zero_of_le_quarter a p N (hr.2.trans hquarter))
    ⟨ht.1, le_refl t⟩

/-- Apply the existence construction to the paper's actual delayed forcing
from a supplied source. This does not yet solve the coupled tracking system. -/
theorem exists_delayed_forcedColeHopf_mild (a β : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (p : BUC E ℝ) (N : ℝ → BUC E ℝ) :
    ∃ ξ : ℝ → BUC E ℝ,
      IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧
      ∀ t ∈ Icc 0 T, t ≤ 1 / 4 → ξ t = 0 := by
  obtain ⟨ξ, hξ⟩ := exists_forcedColeHopf_mild a β hT (delayedHeatForcing a p N)
    (continuous_delayedHeatForcing a p N).continuousOn
  exact ⟨ξ, hξ, fun _ ht hquarter ↦ hξ.delayed_initial_zero ht hquarter⟩

/-- The phase is unique in the class whose Cole--Hopf transforms satisfy
the mild equation. Classical-to-mild regularity is not presumed here. -/
theorem eqOn_of_forcedColeHopf_transform {a β T : ℝ} {g σ τ : ℝ → BUC E ℝ}
    (hσ : IsForcedColeHopfMild a β g (fun t ↦ coleHopfBUC β (σ t)) T)
    (hτ : IsForcedColeHopfMild a β g (fun t ↦ coleHopfBUC β (τ t)) T)
    (hg : ContinuousOn g (Icc 0 T)) (hT : 0 ≤ T) : EqOn σ τ (Icc 0 T) := by
  intro t ht
  have heq := hσ.unique hτ hg hT ht
  ext x
  apply (strictMono_coleHopf β).injective
  exact congrArg (fun u : BUC E ℝ ↦ u x) heq

/-- A canonical finite-horizon solution; its values on the horizon are
independent of the choice made in this definition. -/
def forcedColeHopfMildSolution (a β : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (g : ℝ → BUC E ℝ) (hg : ContinuousOn g (Icc 0 T)) : ℝ → BUC E ℝ :=
  (exists_forcedColeHopf_mild a β hT g hg).choose

theorem isForcedColeHopfMild_solution (a β : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (g : ℝ → BUC E ℝ) (hg : ContinuousOn g (Icc 0 T)) :
    IsForcedColeHopfMild a β g (forcedColeHopfMildSolution a β hT g hg) T :=
  (exists_forcedColeHopf_mild a β hT g hg).choose_spec

/-- Enlarging the final time does not alter the constructed solution on
the earlier interval. -/
theorem forcedColeHopfMildSolution_consistent (a β : ℝ) {S T : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (g : ℝ → BUC E ℝ) (hgS : ContinuousOn g (Icc 0 S)) (hgT : ContinuousOn g (Icc 0 T)) :
    EqOn (forcedColeHopfMildSolution a β hS g hgS)
      (forcedColeHopfMildSolution a β hT g hgT) (Icc 0 S) :=
  (isForcedColeHopfMild_solution a β hS g hgS).unique
    ((isForcedColeHopfMild_solution a β hT g hgT).mono hST) hgS hS

/-- Existence and the uniform zero-order phase estimate, with constants
chosen before the forcing and time interval. This is the continuous mild
part of Lemma `lem:xiAP`, not its remaining smoothness assertion. -/
theorem exists_forcedColeHopf_mild_phase (β C : ℝ) (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0, ∀ (a T M : ℝ) (g : ℝ → BUC E ℝ),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ContinuousOn g (Icc 0 T) →
      (∀ t ∈ Icc 0 T, ‖g t‖ ≤ C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      ∃ ξ σ : ℝ → BUC E ℝ,
        IsForcedColeHopfMild a β g ξ T ∧ ContinuousOn σ (Icc 0 T) ∧ σ 0 = 0 ∧
        (∀ t ∈ Icc 0 T, ‖ξ t‖ ≤ C₀ * M ∧ |β| * ‖ξ t‖ ≤ 1 / 2 ∧
          ‖σ t‖ ≤ (2 * C₀) * M ∧ (∀ x, σ t x = coleHopfInv β (ξ t x)) ∧
          coleHopfBUC β (σ t) = ξ t) ∧
        (∀ η, IsForcedColeHopfMild a β g η T → EqOn η ξ (Icc 0 T)) := by
  obtain ⟨C₀, hC₀, M₀, hM₀, hb⟩ := exists_forcedColeHopf_small_bound (E := E) β C hC
  refine ⟨C₀, hC₀, M₀, hM₀, ?_⟩
  intro a T M g hT hM hMM hg hdecay
  obtain ⟨ξ, hξ⟩ := exists_forcedColeHopf_mild a β hT g hg
  have hbound := hb a T M g ξ hT hM hMM hg hdecay hξ
  obtain ⟨σ, hσc, hσ⟩ := exists_continuous_coleHopfInv_on ξ hξ.continuous
    (fun t ht ↦ (hbound t ht).2)
  refine ⟨ξ, σ, hξ, hσc, ?_, ?_, fun η hη ↦ hη.unique hξ hg hT⟩
  · ext x
    rw [(hσ 0 ⟨le_refl 0, hT⟩).1 x, hξ.initial hT]
    simp
  · intro t ht
    refine ⟨(hbound t ht).1, (hbound t ht).2, ?_, (hσ t ht).1, (hσ t ht).2.1⟩
    calc
      ‖σ t‖ ≤ 2 * ‖ξ t‖ := (hσ t ht).2.2
      _ ≤ 2 * (C₀ * M) := mul_le_mul_of_nonneg_left (hbound t ht).1 (by norm_num)
      _ = _ := by ring

end

end Planarwave
