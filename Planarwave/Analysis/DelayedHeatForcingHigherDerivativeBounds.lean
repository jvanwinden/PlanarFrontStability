/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatHigherDerivativeBounds
public import Planarwave.Analysis.DelayedHeatForcingRegularity
public import Planarwave.Analysis.DelayedHeatForcingSmoothing
public import Planarwave.Analysis.DelayedPolynomialDecay

@[expose] public section

/-!
# All-order spatial bounds for the delayed forcing

This proves the `C^9` forcing estimate `eq:gest` used before Step 1 of
`lem:key`, in fact at every finite spatial order. The cutoff leaves a heat
age of at least `1/4`; reserving `1/8` for differentiation also gives the
smoothed-source version used after Lemma 4.2. No spatial derivative of the
source is assumed.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

/-- One constant controls every derivative through order `K` at heat age `1/8`. -/
def delayedForcingSpatialConstant (a : ℝ) (K : ℕ) : ℝ :=
  (max 1 (heatScale a ((1 / 8) / (K + 1)))⁻¹) ^ K

theorem delayedForcingSpatialConstant_pos (a : ℝ) (K : ℕ) :
    0 < delayedForcingSpatialConstant a K := by
  unfold delayedForcingSpatialConstant
  exact pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)) _

universe u

variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance delayedHigherTensorNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (E [×k]→L[ℝ] F) := inferInstance
local instance delayedHigherTensorNormedSpace (k : ℕ) :
    NormedSpace ℝ (E [×k]→L[ℝ] F) := inferInstance
local instance delayedHigherBUCNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (BUC E (E [×k]→L[ℝ] F)) := inferInstance

/-- The cutoff removes the singularity of every spatial derivative at age zero. -/
theorem norm_iteratedFDeriv_trackingHeatPulse_le {a : ℝ} (ha : 0 < a)
    (K k : ℕ) (hk : k ≤ K) (f : BUC E F) (t : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y ↦ trackingCutoff t • heatFlow a t f y) x‖ ≤
      trackingCutoff t * (delayedForcingSpatialConstant a K * ‖f‖) := by
  by_cases hρ : trackingCutoff t = 0
  · simp only [hρ, zero_smul, zero_mul]
    change ‖iteratedFDeriv ℝ k (0 : E → F) x‖ ≤ 0
    simp
  have ht : (1 : ℝ) / 8 ≤ t := by linarith [(trackingCutoff_ne_zero_mem hρ).1]
  rw [iteratedFDeriv_const_smul_apply'
    (contDiff_nat_heatFlow k ha (by linarith) f).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (trackingCutoff_nonneg t)]
  exact mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_heatFlow_le_of_age K k ha (by norm_num) hk ht f x)
    (trackingCutoff_nonneg t)

/-- All initial-pulse derivatives are bounded by the initial supremum norm. -/
theorem norm_iteratedFDeriv_delayedHeatForcing_initial_le {a : ℝ} (ha : 0 < a)
    (K k : ℕ) (hk : k ≤ K) (p : BUC E F) (N : ℝ → BUC E F)
    {t : ℝ} (ht : t ≤ 1) (x : E) :
    ‖iteratedFDeriv ℝ k (delayedHeatForcing a p N t : E → F) x‖ ≤
      trackingCutoff t * (delayedForcingSpatialConstant a K * ‖p‖) := by
  rw [delayedHeatForcing_initial a p N ht]
  exact norm_iteratedFDeriv_trackingHeatPulse_le ha K k hk p t x

/-- Each completed block supplies bounds for all spatial derivatives of its pulse. -/
theorem norm_iteratedFDeriv_delayedHeatForcing_block_le {a : ℝ} (ha : 0 < a)
    (K k : ℕ) (hk : k ≤ K) (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ)
    {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1), ‖N r‖ ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ k (delayedHeatForcing a p N ((n : ℝ) + 1 + τ) : E → F) x‖ ≤
      trackingCutoff τ * (delayedForcingSpatialConstant a K * M) := by
  rw [delayedHeatForcing_block a p N n hτ]
  exact (norm_iteratedFDeriv_trackingHeatPulse_le ha K k hk (delayedHeatBlock a N n) τ x).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (norm_delayedHeatBlock_le a N n hN) (delayedForcingSpatialConstant_pos a K).le)
      (trackingCutoff_nonneg τ))

/-- The same all-order estimate uses only the source smoothed for time `1/8`.
This is the derivative version of the factorization preceding Lemma 4.2's use. -/
theorem norm_iteratedFDeriv_delayedHeatForcing_block_smoothed_le {a : ℝ} (ha : 0 < a)
    (K k : ℕ) (hk : k ≤ K) (p : BUC E F) (N : ℝ → BUC E F) (n : ℕ)
    {τ M : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hN : ContinuousOn N (Icc (n : ℝ) ((n : ℝ) + 1)))
    (hbound : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1), ‖heatFlowBUC a (1 / 8) (N r)‖ ≤ M)
    (x : E) :
    ‖iteratedFDeriv ℝ k (delayedHeatForcing a p N ((n : ℝ) + 1 + τ) : E → F) x‖ ≤
      trackingCutoff τ * (delayedForcingSpatialConstant a K * M) := by
  rw [delayedHeatForcing_block_smoothed ha.le p N n hτ hN]
  by_cases hρ : trackingCutoff τ = 0
  · simp only [hρ, zero_smul, BUC.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, norm_zero,
      zero_mul, le_refl]
  have hage : (1 : ℝ) / 8 ≤ τ - 1 / 8 := by linarith [(trackingCutoff_ne_zero_mem hρ).1]
  let b := delayedHeatBlock a (fun r ↦ heatFlowBUC a (1 / 8) (N r)) n
  change ‖iteratedFDeriv ℝ k (fun y ↦ trackingCutoff τ • heatFlow a (τ - 1 / 8) b y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    (contDiff_nat_heatFlow k ha (by linarith) b).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (trackingCutoff_nonneg τ)]
  apply mul_le_mul_of_nonneg_left _ (trackingCutoff_nonneg τ)
  exact (norm_iteratedFDeriv_heatFlow_le_of_age K k ha (by norm_num) hk hage b x).trans
    (mul_le_mul_of_nonneg_left (norm_delayedHeatBlock_le a _ n hbound)
      (delayedForcingSpatialConstant_pos a K).le)

/-- Polynomial source decay is inherited by every derivative through order `K`.
The constant is uniform in the time horizon, source, initial datum, and spatial point. -/
theorem norm_iteratedFDeriv_delayedHeatForcing_decay_le {a γ T M : ℝ}
    (ha : 0 < a) (hγ : 0 ≤ γ) (K k : ℕ) (hk : k ≤ K)
    (p : BUC E F) (N : ℝ → BUC E F) (hM : 0 ≤ M) (hp : ‖p‖ ≤ M)
    (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ k (delayedHeatForcing a p N t : E → F) x‖ ≤
      (‖trackingCutoff‖ * delayedForcingSpatialConstant a K * (3 : ℝ) ^ γ) *
        M * (1 + t) ^ (-γ) := by
  have hH := (delayedForcingSpatialConstant_pos a K).le
  apply le_decay_of_delayed_block_bounds hγ (mul_nonneg (norm_nonneg _) hH) hM ?_ ?_ ht
  · intro r _ hr
    calc
      _ ≤ trackingCutoff r * (delayedForcingSpatialConstant a K * ‖p‖) :=
        norm_iteratedFDeriv_delayedHeatForcing_initial_le ha K k hk p N hr x
      _ ≤ ‖trackingCutoff‖ * (delayedForcingSpatialConstant a K * M) := by
        gcongr
        exact trackingCutoff_le_norm r
      _ = _ := by ring
  · intro n τ hτ hτT
    have hblock : ∀ r ∈ Icc (n : ℝ) ((n : ℝ) + 1), ‖N r‖ ≤ M * (1 + (n : ℝ)) ^ (-γ) := by
      intro r hr
      have hrT : r ∈ Icc 0 T := ⟨(Nat.cast_nonneg n).trans hr.1, by linarith [hr.2, hτ.1]⟩
      exact (hN r hrT).trans (mul_le_mul_of_nonneg_left
        (one_add_rpow_neg_antitone hγ (Nat.cast_nonneg n) hr.1) hM)
    calc
      _ ≤ trackingCutoff τ * (delayedForcingSpatialConstant a K *
          (M * (1 + (n : ℝ)) ^ (-γ))) :=
        norm_iteratedFDeriv_delayedHeatForcing_block_le ha K k hk p N n hτ hblock x
      _ ≤ ‖trackingCutoff‖ * (delayedForcingSpatialConstant a K *
          (M * (1 + (n : ℝ)) ^ (-γ))) :=
        mul_le_mul_of_nonneg_right (trackingCutoff_le_norm τ) (by positivity)
      _ = _ := by ring

/-- The forcing derivatives in the all-order decay estimate belong to BUC.
Uniform continuity follows from the bound one order higher. -/
theorem exists_buc_iteratedFDeriv_delayedHeatForcing {a γ T M : ℝ}
    (ha : 0 < a) (hγ : 0 ≤ γ) (K k : ℕ) (hk : k ≤ K)
    (p : BUC E F) (N : ℝ → BUC E F) (hM : 0 ≤ M) (hp : ‖p‖ ≤ M)
    (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-γ))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ g : BUC E (E [×k]→L[ℝ] F),
      (∀ x, g x = iteratedFDeriv ℝ k (delayedHeatForcing a p N t : E → F) x) ∧
      ‖g‖ ≤ (‖trackingCutoff‖ * delayedForcingSpatialConstant a K * (3 : ℝ) ^ γ) *
        M * (1 + t) ^ (-γ) := by
  have hf : ContDiff ℝ ∞ (delayedHeatForcing a p N t : E → F) := by
    simpa only [Function.comp_def] using!
      (contDiff_delayedHeatForcing ha p N).comp (f := fun x : E ↦ (t, x))
        (contDiff_const.prodMk contDiff_id)
  exact exists_buc_iteratedFDeriv_of_bounds
    (hf.of_le (WithTop.coe_le_coe.mpr (show (↑(k + 1) : ℕ∞) ≤ ⊤ from le_top)))
    (norm_iteratedFDeriv_delayedHeatForcing_decay_le ha hγ K k hk p N hM hp hN ht)
    (norm_iteratedFDeriv_delayedHeatForcing_decay_le ha hγ (K + 1) (k + 1)
      (Nat.succ_le_succ hk) p N hM hp hN ht)

end

end Planarwave
