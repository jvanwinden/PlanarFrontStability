/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupPerturbation
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Generator of the bounded-perturbation semigroup

The Duhamel term has derivative `f(0)` at zero for continuous forcing `f`. Applied to the
bounded-coefficient mild equation, this identifies both directions of the generator relation:
the domain is unchanged and the generator is `A + B`.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Rescaling the integration interval makes the derivative of the forcing at zero explicit. -/
theorem hasDerivAt_duhamel_zero (S : C0Semigroup ℂ E) {f : ℝ → E} (hf : Continuous f) :
    HasDerivAt (S.duhamel f) (f 0) 0 := by
  let F : ℝ → E := fun t ↦ ∫ r in (0 : ℝ)..1, S.realOrbit (f (t * r)) (t - t * r)
  have hF : Continuous F := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact S.continuous_realOrbit_joint.comp
      ((continuous_fst.sub (continuous_fst.mul continuous_snd)).prodMk
        (hf.comp (continuous_fst.mul continuous_snd)))
  have hF0 : F 0 = f 0 := by simp [F]
  have hlim : Tendsto F (𝓝[≠] (0 : ℝ)) (𝓝 (f 0)) := by
    rw [← hF0]
    exact hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hasDerivAt_iff_tendsto_slope]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have heq : F t = t⁻¹ • S.duhamel f t := by
    simpa only [mul_zero, mul_one, F, duhamel] using!
      (intervalIntegral.integral_comp_mul_left
        (fun r ↦ S.realOrbit (f r) (t - r)) ht0 (a := 0) (b := 1))
  simpa only [slope, vsub_eq_sub, sub_zero, duhamel_zero] using heq

/-- Bounded perturbation preserves the full generator domain and adds the bounded operator. -/
theorem boundedPerturbation_hasGeneratorAt_iff (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (x y : E) :
    (S.boundedPerturbation B).HasGeneratorAt x y ↔ S.HasGeneratorAt x (y - B x) := by
  have hd : HasDerivWithinAt
      (S.duhamel (fun r ↦ B (S.perturbedOrbit B x r))) (B x) (Ici 0) 0 := by
    have h := S.hasDerivAt_duhamel_zero
      (f := fun r ↦ B (S.perturbedOrbit B x r))
      (B.continuous.comp (S.continuous_perturbedOrbit B x))
    simpa only [perturbedOrbit, Real.toNNReal_zero, perturbedOperator_zero] using!
      h.hasDerivWithinAt (s := Ici 0)
  constructor
  · intro h
    apply (h.sub hd).congr
    · intro t ht
      change S.realOrbit x t = S.perturbedOrbit B x t -
        S.duhamel (fun r ↦ B (S.perturbedOrbit B x r)) t
      rw [S.perturbedOrbit_eq B x ht, add_sub_cancel_right]
    · simp
  · intro h
    have hsum := h.add hd
    have hsum' : HasDerivWithinAt
        (fun t ↦ S.realOrbit x t + S.duhamel (fun r ↦ B (S.perturbedOrbit B x r)) t)
        y (Ici 0) 0 := by
      simpa only [sub_add_cancel] using! hsum
    apply hsum'.congr
    · intro t ht
      exact S.perturbedOrbit_eq B x ht
    · simp

/-- The forward generator formula, in the customary `A x + B x` form. -/
theorem HasGeneratorAt.boundedPerturbation {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) (B : E →L[ℂ] E) :
    (S.boundedPerturbation B).HasGeneratorAt x (y + B x) := by
  rw [S.boundedPerturbation_hasGeneratorAt_iff]
  simpa only [add_sub_cancel_right] using h

end

end C0Semigroup
