/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatHigherRegularity
public import Planarwave.Analysis.DelayedHeatForcingHigherRegularity
public import Planarwave.Analysis.ForcedColeHopfExistence

@[expose] public section

/-!
# Arbitrary spatial regularity of the forced Cole--Hopf solution

Rewrite the mild equation as a scalar-coefficient heat Volterra equation
and apply the all-order regularity theorem. For the actual delayed forcing
this needs no derivatives of its source. These results prove spatial
smoothness and BUC time continuity of the solution's derivatives; the
quantitative, horizon-independent `C^k` estimate is a separate obligation.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Regularity of the forcing produces genuine spatial derivatives of the
existing mild solution, rather than an assumed formal derivative equation. -/
theorem IsForcedColeHopfMild.bucSpatialRegularOn {a β T : ℝ} {g ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β g ξ T) (hT : 0 ≤ T) (k : ℕ)
    (hg : BUCSpatialRegularOn (Icc 0 T) k g) :
    BUCSpatialRegularOn (Icc 0 T) k ξ := by
  apply bucSpatialRegularOn_scalar_heatVolterra a hT k
    (fun r ↦ (-β) • g r) (fun t ↦ -heatDuhamel a g t) ξ
    (hg.const_smul (-β)) (hg.heatDuhamel a hT).neg hξ.continuous
  intro t ht
  have hp : ContinuousOn (fun r ↦ BUC.smulBUC (g r) (ξ r)) (Icc 0 t) :=
    ((BUC.continuous_bilinearBUC (ContinuousLinearMap.lsmul ℝ ℝ)).comp_continuousOn
      (hg.continuous.prodMk hξ.continuous)).mono (Icc_subset_Icc le_rfl ht.2)
  have heq : (fun r ↦ BUC.smulBUC ((-β) • g r) (ξ r)) =
      (fun r ↦ (-β) • BUC.smulBUC (g r) (ξ r)) := by
    funext r
    ext x
    simp only [BUC.smulBUC_apply, BUC.smul_apply, smul_eq_mul]
    ring
  rw [hξ.duhamel t ht]
  simp only [forcedColeHopfSource]
  rw [heatDuhamel_add_on a ht.1 (f := g) (g := fun r ↦ β • BUC.smulBUC (g r) (ξ r))
    (hg.continuous.mono (Icc_subset_Icc le_rfl ht.2))
    (hp.const_smul β), heatDuhamel_smul, heq, heatDuhamel_smul, neg_smul]
  abel

/-- For the actual delayed forcing, all BUC spatial derivative trajectories
exist and are continuous on the horizon, without source regularity hypotheses. -/
theorem IsForcedColeHopfMild.delayed_bucSpatialRegularOn {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) (hT : 0 ≤ T) (k : ℕ) :
    BUCSpatialRegularOn (Icc 0 T) k ξ :=
  hξ.bucSpatialRegularOn hT k (bucSpatialRegularOn_delayedHeatForcing k ha p N T)

/-- Every spatial slice of the delayed-forcing solution is smooth, including
the initial time. The result applies to the same previously constructed solution. -/
theorem IsForcedColeHopfMild.delayed_contDiff_infty {a β T : ℝ}
    {p : BUC E ℝ} {N ξ : ℝ → BUC E ℝ}
    (hξ : IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T)
    (ha : 0 < a) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (ξ t : E → ℝ) :=
  contDiff_infty.mpr fun k ↦
    (hξ.delayed_bucSpatialRegularOn ha (ht.1.trans ht.2) k).contDiff ht

/-- Construct a solution with all spatial BUC derivative paths at once.
This does not yet claim uniform-in-horizon bounds for those derivatives. -/
theorem exists_delayed_forcedColeHopf_mild_spatially_smooth {a : ℝ} (ha : 0 < a)
    (β : ℝ) {T : ℝ} (hT : 0 ≤ T) (p : BUC E ℝ) (N : ℝ → BUC E ℝ) :
    ∃ ξ : ℝ → BUC E ℝ,
      IsForcedColeHopfMild a β (delayedHeatForcing a p N) ξ T ∧
      (∀ k : ℕ, BUCSpatialRegularOn (Icc 0 T) k ξ) ∧
      ∀ t ∈ Icc 0 T, t ≤ 1 / 4 → ξ t = 0 := by
  obtain ⟨ξ, hξ, hz⟩ := exists_delayed_forcedColeHopf_mild a β hT p N
  exact ⟨ξ, hξ, fun k ↦ hξ.delayed_bucSpatialRegularOn ha hT k, hz⟩

end

end Planarwave
