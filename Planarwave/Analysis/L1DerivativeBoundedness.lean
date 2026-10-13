/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Boundedness from an integrable longitudinal derivative

An integrable function with integrable derivative vanishes at infinity. The
fundamental theorem of calculus then bounds its supremum norm by the L1 norm
of its derivative. Applied to an adjoint two-jet, this gives uniform bounds
and a common Lipschitz constant from the L1 elliptic estimate.
-/

open MeasureTheory Set

namespace Planarwave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A whole-line W1,1 bound, obtained from the zero limit at positive infinity. -/
theorem norm_le_integral_norm_derivative {u v : ℝ → F}
    (hu : Integrable u) (hv : Integrable v) (hd : ∀ x, HasDerivAt u (v x) x) (x : ℝ) :
    ‖u x‖ ≤ ∫ t, ‖v t‖ := by
  have hzero := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (a := x) (fun y _ ↦ hd y) hv.integrableOn hu.integrableOn
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := x) (fun y _ ↦ hd y) hv.integrableOn hzero
  calc
    _ = ‖∫ t in Ioi x, v t‖ := by rw [hFTC, zero_sub, norm_neg]
    _ ≤ ∫ t in Ioi x, ‖v t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖v t‖ := integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun t ↦ norm_nonneg _) hv.norm

/-- The same bound in the BUC norm. -/
theorem buc_norm_le_integral_norm_derivative (u : BUC ℝ F) {v : ℝ → F}
    (hu : Integrable (u : ℝ → F)) (hv : Integrable v)
    (hd : ∀ x, HasDerivAt u (v x) x) : ‖u‖ ≤ ∫ t, ‖v t‖ :=
  (BUC.norm_le (integral_nonneg fun _ ↦ norm_nonneg _)).mpr
    (norm_le_integral_norm_derivative hu hv hd)

end Planarwave
