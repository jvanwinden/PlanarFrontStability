/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfBounds

@[expose] public section

/-!
# Grönwall for a common derivative-norm majorant

In the paper's C^k estimate the same forcing norm bounds every component
of a derivative jet. This scalar version of the integrable-decay argument
applies to their maximum, without requiring that maximum to solve a PDE.
-/

open MeasureTheory Set

namespace Planarwave

/-- A common forcing majorant of total mass `A` gives the uniform
Grönwall bound `A exp(K A)`. -/
theorem le_mul_exp_of_integral_majorant {u ρ : ℝ → ℝ} {T K A : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hu : ContinuousOn u (Icc 0 T)) (hρ : ContinuousOn ρ (Icc 0 T))
    (hρ0 : ∀ r ∈ Icc 0 T, 0 ≤ ρ r)
    (hi : ∀ t ∈ Icc 0 T, u t ≤ ∫ r in (0 : ℝ)..t, ρ r * (1 + K * u r))
    (hmass : ∀ t ∈ Icc 0 T, (∫ r in (0 : ℝ)..t, ρ r) ≤ A)
    {t : ℝ} (ht : t ∈ Icc 0 T) : u t ≤ A * Real.exp (K * A) := by
  have hlin : ∀ s ∈ Icc 0 T, u s ≤ A + ∫ r in (0 : ℝ)..s, (K * ρ r) * u r := by
    intro s hs
    have h1 := (hρ.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc (μ := volume) hs.1
    have h2 : IntervalIntegrable (fun r ↦ (K * ρ r) * u r) volume 0 s :=
      (((hρ.const_mul K).mul hu).mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    calc
      _ ≤ ∫ r in (0 : ℝ)..s, ρ r * (1 + K * u r) := hi s hs
      _ = (∫ r in (0 : ℝ)..s, ρ r) + ∫ r in (0 : ℝ)..s, (K * ρ r) * u r := by
        rw [← intervalIntegral.integral_add h1 h2]
        congr 1
        funext r
        ring
      _ ≤ _ := add_le_add (hmass s hs) le_rfl
  apply (le_exp_integral_of_le_add_integral_mul hT hu (hρ.const_mul K)
    (fun r hr ↦ mul_nonneg hK (hρ0 r hr)) hlin t ht).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hmass t ht) hK

/-- The exact integrable decay used in `lem:xiAP` gives a bound linear
in `M`, with no dependence on the final time. -/
theorem le_uniform_of_integral_decay {u ρ : ℝ → ℝ} {T K C M : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hu : ContinuousOn u (Icc 0 T)) (hρ : ContinuousOn ρ (Icc 0 T))
    (hρ0 : ∀ r ∈ Icc 0 T, 0 ≤ ρ r)
    (hi : ∀ t ∈ Icc 0 T, u t ≤ ∫ r in (0 : ℝ)..t, ρ r * (1 + K * u r))
    (hdecay : ∀ t ∈ Icc 0 T, ρ t ≤ C * M * (1 + t) ^ (-(5 : ℝ) / 4))
    {t : ℝ} (ht : t ∈ Icc 0 T) : u t ≤ (4 * C * Real.exp (4 * K * C)) * M := by
  have hmass : ∀ s ∈ Icc 0 T, (∫ r in (0 : ℝ)..s, ρ r) ≤ 4 * C * M := by
    intro s hs
    have hw : ContinuousOn (fun r : ℝ ↦ (1 + r) ^ (-(5 : ℝ) / 4)) (Icc 0 s) :=
      (continuousOn_const.add continuousOn_id).rpow_const
        (fun r hr ↦ Or.inl (by change 1 + r ≠ 0; linarith [hr.1]))
    calc
      _ ≤ ∫ r in (0 : ℝ)..s, C * M * (1 + r) ^ (-(5 : ℝ) / 4) :=
        intervalIntegral.integral_mono_on hs.1
          ((hρ.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1)
          ((hw.const_mul (C * M)).intervalIntegrable_of_Icc hs.1)
          (fun r hr ↦ hdecay r ⟨hr.1, hr.2.trans hs.2⟩)
      _ = (C * M) * ∫ r in (0 : ℝ)..s, (1 + r) ^ (-(5 : ℝ) / 4) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (C * M) * 4 := mul_le_mul_of_nonneg_left
        (integral_one_add_rpow_neg_five_quarters_le hs.1) (mul_nonneg hC hM)
      _ = _ := by ring
  calc
    u t ≤ (4 * C * M) * Real.exp (K * (4 * C * M)) :=
      le_mul_exp_of_integral_majorant hT hK (by positivity) hu hρ hρ0 hi hmass ht
    _ ≤ (4 * C * M) * Real.exp (4 * K * C) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      calc
        K * (4 * C * M) = (4 * K * C) * M := by ring
        _ ≤ (4 * K * C) * 1 := mul_le_mul_of_nonneg_left hM1 (by positivity)
        _ = _ := mul_one _
    _ = _ := by ring

end Planarwave
