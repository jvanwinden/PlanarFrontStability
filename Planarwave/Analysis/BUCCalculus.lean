/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# From pointwise time derivatives to derivatives in BUC

The longitudinal generator must be identified in the supremum norm. A continuous BUC-valued
candidate derivative, together with its pointwise derivative identities, suffices: the
fundamental theorem of calculus first gives a BUC-valued integral identity, which can then be
differentiated in the Banach space itself.
-/

open Filter MeasureTheory Set Topology

namespace BUC

variable {α F : Type*} [UniformSpace α] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- Integrate continuous pointwise time derivatives as a BUC-valued identity. -/
theorem integral_eq_sub_of_pointwise {u v : ℝ → BUC α F}
    (hu : Continuous u) (hv : Continuous v)
    (hderiv : ∀ t > 0, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in 0..t, v r) = u t - u 0 := by
  ext x
  change evalCLM (𝕜 := ℝ) x (∫ r in 0..t, v r) = u t x - u 0 x
  rw [← (evalCLM (𝕜 := ℝ) x).intervalIntegral_comp_comm (hv.intervalIntegrable _ _)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (((evalCLM (𝕜 := ℝ) x).continuous.comp hu).continuousOn)
    (fun r hr ↦ hderiv r hr.1 x)
    (((evalCLM (𝕜 := ℝ) x).continuous.comp hv).intervalIntegrable _ _)

/-- Continuous pointwise derivatives yield a supremum-norm derivative at positive times. -/
theorem hasDerivAt_of_pointwise {u v : ℝ → BUC α F}
    (hu : Continuous u) (hv : Continuous v)
    (hderiv : ∀ t > 0, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t)
    {t : ℝ} (ht : 0 < t) : HasDerivAt u (v t) t := by
  have h := (intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt).add_const (u 0)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  rw [integral_eq_sub_of_pointwise hu hv hderiv hr.le, sub_add_cancel]

/-- The same argument gives the right derivative at the initial time, the defining generator
limit for a strongly continuous semigroup. -/
theorem hasDerivWithinAt_zero_of_pointwise {u v : ℝ → BUC α F}
    (hu : Continuous u) (hv : Continuous v)
    (hderiv : ∀ t > 0, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t) :
    HasDerivWithinAt u (v 0) (Ici 0) 0 := by
  have h := (intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 0)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt).add_const (u 0)
  apply h.hasDerivWithinAt.congr
  · intro r hr
    rw [integral_eq_sub_of_pointwise hu hv hderiv hr, sub_add_cancel]
  · simp

end BUC
