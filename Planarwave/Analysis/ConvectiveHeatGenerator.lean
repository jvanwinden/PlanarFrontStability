/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCCalculus
public import Planarwave.Analysis.ConvectiveHeatSemigroup
public import Planarwave.Analysis.HeatJointSmoothReal
public import Planarwave.Analysis.ComplexBUC2

@[expose] public section

/-!
# The convective heat generator on the common longitudinal domain

For BUC data with two BUC derivatives the right derivative at time zero is `a f'' + c f'`,
in the BUC norm. This identifies the generator action needed by the diagonalization argument
in the proof of Lemma 2.2, including the Fourier damping term `-q a f`.
-/

open Set

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Spatial differentiation commutes with heat flow followed by constant translation. -/
theorem hasDerivAt_convectiveHeatFlow_space (a t c : ℝ) (f g : BUC ℝ F)
    (hfg : ∀ x, HasDerivAt f (g x) x) (x : ℝ) :
    HasDerivAt (convectiveHeatFlowBUC a t c f)
      (convectiveHeatFlowBUC a t c g x) x := by
  change HasDerivAt (fun y ↦ convectiveHeatFlowBUC a t c f y) _ x
  have h := (hasDerivAt_heatFlow_of_hasDerivAt a t f g hfg (x + t * c)).scomp x
    ((hasDerivAt_id x).add_const (t * c))
  simpa [Function.comp_def, convectiveHeatFlowBUC_apply] using h

/-- Positive-time convective heat evolution has two successive BUC derivatives. -/
theorem exists_buc_derivatives_convectiveHeatFlow {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (c : ℝ) (f : BUC ℝ F) : ∃ g h : BUC ℝ F,
    (∀ x, HasDerivAt (convectiveHeatFlowBUC a t c f) (g x) x) ∧
    (∀ x, HasDerivAt g (h x) x) := by
  obtain ⟨g, h, hg, hh⟩ := exists_buc_derivatives_heatFlow_real ha ht f
  refine ⟨BUC.translate (-(t * c)) g, BUC.translate (-(t * c)) h, ?_, ?_⟩
  · intro x
    change HasDerivAt (fun y ↦ convectiveHeatFlowBUC a t c f y) _ x
    simpa [Function.comp_def, convectiveHeatFlowBUC_apply] using
      (hg (x + t * c)).scomp x ((hasDerivAt_id x).add_const (t * c))
  · intro x
    change HasDerivAt (fun y ↦ BUC.translate (-(t * c)) g y) _ x
    simpa [Function.comp_def] using
      (hh (x + t * c)).scomp x ((hasDerivAt_id x).add_const (t * c))

/-- The convective heat equation on data with two BUC derivatives, first pointwise in space. -/
theorem hasDerivAt_convectiveHeatFlow_pointwise {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (c : ℝ) (f g h : BUC ℝ F)
    (hfg : ∀ x, HasDerivAt f (g x) x) (hgh : ∀ x, HasDerivAt g (h x) x) (x : ℝ) :
    HasDerivAt (fun r ↦ convectiveHeatFlowBUC a r c f x)
      (a • convectiveHeatFlowBUC a t c h x + c • convectiveHeatFlowBUC a t c g x) t := by
  have hd := (hasFDerivAt_heatFlow_uncurry_real ha f (t, x + t * c) ht).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (((hasDerivAt_id t).mul_const c).const_add x))
  rw [deriv_heatFlow_of_hasDerivAt a t f g hfg,
    deriv_heatFlow_of_hasDerivAt a t g h hgh] at hd
  simpa [Function.comp_def, convectiveHeatFlowBUC_apply] using hd

/-- The convective heat equation holds in the supremum norm on twice differentiable BUC data. -/
theorem hasDerivAt_convectiveHeatFlowBUC {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (c : ℝ) (f g h : BUC ℝ F)
    (hfg : ∀ x, HasDerivAt f (g x) x) (hgh : ∀ x, HasDerivAt g (h x) x) :
    HasDerivAt (fun r ↦ convectiveHeatFlowBUC a r c f)
      (a • convectiveHeatFlowBUC a t c h + c • convectiveHeatFlowBUC a t c g) t := by
  apply BUC.hasDerivAt_of_pointwise (continuous_convectiveHeatFlowBUC_time a c f)
    (((continuous_convectiveHeatFlowBUC_time a c h).const_smul a).add
      ((continuous_convectiveHeatFlowBUC_time a c g).const_smul c))
    (fun r hr x ↦ hasDerivAt_convectiveHeatFlow_pointwise ha hr c f g h hfg hgh x) ht

/-- The right generator limit for the convective heat semigroup, in BUC norm. -/
theorem hasDerivWithinAt_convectiveHeatFlowBUC_zero {a : ℝ} (ha : 0 < a)
    (c : ℝ) (f g h : BUC ℝ F)
    (hfg : ∀ x, HasDerivAt f (g x) x) (hgh : ∀ x, HasDerivAt g (h x) x) :
    HasDerivWithinAt (fun r ↦ convectiveHeatFlowBUC a r c f)
      (a • h + c • g) (Ici 0) 0 := by
  simpa only [Pi.add_apply, Pi.smul_apply, convectiveHeatFlowBUC_zero] using
    BUC.hasDerivWithinAt_zero_of_pointwise (continuous_convectiveHeatFlowBUC_time a c f)
      (((continuous_convectiveHeatFlowBUC_time a c h).const_smul a).add
        ((continuous_convectiveHeatFlowBUC_time a c g).const_smul c))
      (fun r hr x ↦ hasDerivAt_convectiveHeatFlow_pointwise ha hr c f g h hfg hgh x)

/-- Adding a scalar Fourier damping factor shifts the generator by the expected bounded
zeroth-order term. This is the scalar diagonal operator used in Lemma 2.2. -/
theorem hasDerivWithinAt_dampedConvectiveHeatFlowBUC_zero {a : ℝ} (ha : 0 < a)
    (c q : ℝ) (f g h : BUC ℝ F)
    (hfg : ∀ x, HasDerivAt f (g x) x) (hgh : ∀ x, HasDerivAt g (h x) x) :
    HasDerivWithinAt (fun r ↦ Real.exp ((-q * a) * r) • convectiveHeatFlowBUC a r c f)
      (a • h + c • g - (q * a) • f) (Ici 0) 0 := by
  have he := (Real.hasDerivAt_exp ((-q * a) * 0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_mul (-q * a))
  have hd := he.hasDerivWithinAt.smul
    (hasDerivWithinAt_convectiveHeatFlowBUC_zero ha c f g h hfg hgh)
  simpa [Function.comp_def, Pi.smul_def, sub_eq_add_neg, add_comm, add_left_comm] using! hd

end

end Planarwave
