/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfHigherRegularity
public import Planarwave.Analysis.HeatHigherDuhamelBounds
public import Planarwave.Analysis.IntegrableDecayGronwall
public import Planarwave.Analysis.DelayedHeatForcingHigherDerivativeBounds

@[expose] public section

/-!
# The all-order Cole--Hopf estimate in Lemma `lem:xiAP`

Take the continuous maximum of the genuine BUC derivative norms, apply
the `C^k` product rule to the mild equation, and use the integrable-decay
Grönwall estimate. The constants are independent of the final time. This
is the paper's argument, now for every finite spatial order, including nine.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The arbitrary-order, horizon-independent a priori bound of `lem:xiAP`.
Spatial derivatives are supplied by the regularity theorem, not assumed for `ξ`. -/
theorem IsForcedColeHopfMild.spatial_bound {a β T C M : ℝ}
    {g ξ : ℝ → BUC E ℝ} (hξ : IsForcedColeHopfMild a β g ξ T)
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1) (k : ℕ)
    (hg : BUCSpatialRegularOn (Icc 0 T) k g)
    (hdecay : ∀ t ∈ Icc 0 T, BUCSpatialBound k (g t)
      (C * M * (1 + t) ^ (-(5 : ℝ) / 4)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    BUCSpatialBound k (ξ t) ((4 * C * Real.exp (4 * (|β| * 2 ^ k) * C)) * M) := by
  have hreg := hξ.bucSpatialRegularOn hT k hg
  obtain ⟨U, hUc, hU⟩ := hreg.exists_least_bound
  let ρ := fun r : ℝ ↦ C * M * (1 + r) ^ (-(5 : ℝ) / 4)
  have hρc : ContinuousOn ρ (Icc 0 T) :=
    ((continuousOn_const.add continuousOn_id).rpow_const
      (fun r hr ↦ Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))).const_mul (C * M)
  have hρ0 : ∀ r ∈ Icc 0 T, 0 ≤ ρ r := fun r hr ↦
    mul_nonneg (mul_nonneg hC hM) (Real.rpow_nonneg (by linarith [hr.1]) _)
  have hsource : BUCSpatialRegularOn (Icc 0 T) k
      (fun r ↦ forcedColeHopfSource β (g r) (ξ r)) :=
    hg.add ((hg.bilinear hreg (ContinuousLinearMap.lsmul ℝ ℝ)).const_smul β)
  have hi : ∀ s ∈ Icc 0 T,
      U s ≤ ∫ r in (0 : ℝ)..s, ρ r * (1 + (|β| * 2 ^ k) * U r) := by
    intro s hs
    apply (hU s hs).2
    rw [hξ.duhamel s hs]
    apply BUCSpatialBound.neg
    apply hsource.heatDuhamel_bound a hT (A := fun r ↦ ρ r * (1 + (|β| * 2 ^ k) * U r))
      (hρc.mul (continuousOn_const.add (hUc.const_mul (|β| * 2 ^ k)))) _ hs
    intro r hr
    have hp : BUCSpatialBound k (BUC.smulBUC (g r) (ξ r)) ((2 : ℝ) ^ k * ρ r * U r) := by
      simpa only [ContinuousLinearMap.opNorm_lsmul, mul_one] using!
        (hdecay r hr).bilinear (hU r hr).1 (ContinuousLinearMap.lsmul ℝ ℝ)
    have hb := (hdecay r hr).add (hp.smul β)
    convert hb using 1
    · rfl
    · dsimp only [ρ]
      ring
  have hb : U t ≤ (4 * C * Real.exp (4 * (|β| * 2 ^ k) * C)) * M :=
    le_uniform_of_integral_decay hT (by positivity) hC hM hM1 hUc hρc hρ0 hi
      (fun _ _ ↦ le_rfl) ht
  exact (hU t ht).1.mono hb

end

end Planarwave
