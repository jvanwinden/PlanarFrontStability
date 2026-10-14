/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# Density of the generator domain

Integrating an orbit produces a generator-domain vector. Its short-time averages converge to
the initial datum. This supplies the density needed for uniqueness of a semigroup with a
given generator, and hence for reassociating bounded perturbations in the paper's compact-
family uniformization argument.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The generator relation is preserved by real scalar multiplication. -/
theorem HasGeneratorAt.smul_real {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) (a : ℝ) : S.HasGeneratorAt (a • x) (a • y) := by
  have hd := HasDerivWithinAt.const_smul a h
  apply hd.congr
  · intro r _
    exact ((S r.toNNReal).restrictScalars ℝ).map_smul a x
  · simp

/-- The integral of an orbit belongs to the generator domain. -/
theorem hasGeneratorAt_orbitIntegral (S : C0Semigroup ℂ E) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    S.HasGeneratorAt (∫ r in 0..t, S.realOrbit x r) (S.realOrbit x t - x) := by
  have hc := S.continuous_realOrbit x
  have hder (a : ℝ) : HasDerivAt (fun s ↦ ∫ r in 0..s, S.realOrbit x r) (S.realOrbit x a) a :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 a)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hshift := (hder t).scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).add_const t) (by simp)
  have hd : HasDerivAt
      (fun s : ℝ ↦ (∫ r in 0..s + t, S.realOrbit x r) - ∫ r in 0..s, S.realOrbit x r)
      (S.realOrbit x t - x) 0 := by
    simpa only [Function.comp_def, one_smul, realOrbit_zero] using! hshift.sub (hder 0)
  apply hd.hasDerivWithinAt.congr
  · intro s hs
    change S s.toNNReal (∫ r in 0..t, S.realOrbit x r) = _
    rw [← (S s.toNNReal).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
    calc
      (∫ r in 0..t, S s.toNNReal (S.realOrbit x r)) = ∫ r in 0..t, S.realOrbit x (s + r) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Icc (0 : ℝ) t := uIcc_of_le ht ▸ hr
        exact (S.realOrbit_add x hs hr'.1).symm
      _ = ∫ r in s..s + t, S.realOrbit x r := by
        simpa only [add_zero] using!
          intervalIntegral.integral_comp_add_left (S.realOrbit x) s (a := 0) (b := t)
      _ = _ := by
        have hi := intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable (μ := volume) 0 s) (hc.intervalIntegrable s (s + t))
        exact eq_sub_of_add_eq' hi
  · simp

/-- Every strongly continuous semigroup has a dense generator domain. -/
theorem dense_generatorDomain (S : C0Semigroup ℂ E) : Dense {x : E | ∃ y, S.HasGeneratorAt x y} := by
  intro x
  have hc := S.continuous_realOrbit x
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hlim : Tendsto (fun t : ℝ ↦ t⁻¹ • ∫ r in 0..t, S.realOrbit x r) (𝓝[>] 0) (𝓝 x) := by
    simpa only [zero_add, intervalIntegral.integral_same, sub_zero, realOrbit_zero] using!
      hd.tendsto_slope_zero_right
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ⟨t⁻¹ • (S.realOrbit x t - x), (S.hasGeneratorAt_orbitIntegral x ht.le).smul_real t⁻¹⟩

end

end C0Semigroup
