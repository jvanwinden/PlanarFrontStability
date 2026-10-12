/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCCalculus
public import Planarwave.Analysis.ConvectiveHeatSemigroup
public import Planarwave.Analysis.HeatJointSmoothMultidimensional
public import Planarwave.Analysis.SemigroupGenerator

@[expose] public section

/-!
# The full-dimensional convective heat generator

On data with two BUC Fréchet derivatives, the right derivative at zero in the
supremum norm is `a Δv + Dv b`. This identifies the principal scalar spatial
generator used before adding the front's bounded reaction coefficient.
-/

open MeasureTheory Set
open scoped Laplacian

namespace Planarwave

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Constant bounded linear maps commute with Gaussian averaging. -/
theorem heatFlowBUC_postcomp (a t : ℝ) (L : F →L[ℝ] G) (v : BUC E F) :
    heatFlowBUC a t (BUC.postcompCLM L v) = BUC.postcompCLM L (heatFlowBUC a t v) := by
  ext x
  exact heatFlow_postcompCLM a t L v x

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The trace formula agrees with the Laplacian for two specified Fréchet derivatives. -/
theorem laplacian_eq_trace_of_hasFDerivAt (v : E → F) (g : E → E →L[ℝ] F)
    (h : E → E →L[ℝ] E →L[ℝ] F)
    (hg : ∀ x, HasFDerivAt v (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) (x : E) :
    Δ v x = laplacianTraceCLM (h x) := by
  rw [laplacian_eq_trace_fderiv]
  have hvg : fderiv ℝ v = g := funext fun y ↦ (hg y).fderiv
  rw [hvg, (hh x).fderiv]

/-- The BUC realization of `a Δv + Dv b` from the derivative data. -/
def convectiveGeneratorBUC (a : ℝ) (b : E) (g : BUC E (E →L[ℝ] F))
    (h : BUC E (E →L[ℝ] E →L[ℝ] F)) : BUC E F :=
  a • BUC.postcompCLM (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] F) (F := F) (laplacianTraceCLM (E := E) (F := F)) h +
    BUC.postcompCLM (ContinuousLinearMap.apply ℝ F b) g

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The candidate generator agrees pointwise with the differential expression. -/
theorem convectiveGeneratorBUC_apply (a : ℝ) (b : E) (v : BUC E F)
    (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hg : ∀ x, HasFDerivAt v (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) (x : E) :
    convectiveGeneratorBUC a b g h x = a • Δ (v : E → F) x + fderiv ℝ v x b := by
  rw [laplacian_eq_trace_of_hasFDerivAt _ _ _ hg hh, (hg x).fderiv]
  rfl

/-- The full-dimensional convective heat equation on twice BUC differentiable data. -/
theorem hasDerivAt_convectiveHeatFlow_pointwise_fderiv {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (b : E) (v : BUC E F) (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hg : ∀ x, HasFDerivAt v (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) (x : E) :
    HasDerivAt (fun r ↦ convectiveHeatFlowBUC a r b v x)
      (convectiveHeatFlowBUC a t b (convectiveGeneratorBUC a b g h) x) t := by
  have hd := (differentiableAt_heatFlow_uncurry ha v (t, x + t • b) ht).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (((hasDerivAt_id t).smul_const b).const_add x))
  rw [fderiv_heatFlow_uncurry_apply ha v _ ht] at hd
  simp only [one_smul] at hd
  rw [laplacian_heatFlow_eq_heatFlow a t v g h hg hh,
    fderiv_heatFlow_of_hasFDerivAt a t v g hg] at hd
  have heval := congrArg (fun w : BUC E F ↦ w (x + t • b))
    (heatFlowBUC_postcomp a t (ContinuousLinearMap.apply ℝ F b) g)
  change heatFlow a t (BUC.postcompCLM (ContinuousLinearMap.apply ℝ F b) g) (x + t • b) =
    heatFlow a t g (x + t • b) b at heval
  rw [← heval] at hd
  simpa only [Function.comp_def, id_eq, convectiveHeatFlowBUC_apply, convectiveGeneratorBUC,
    ← heatFlowBUC_apply, heatFlowBUC_add, heatFlowBUC_smul, BUC.add_apply, BUC.smul_apply] using! hd

/-- Right generator limit at time zero, in the full spatial supremum norm. -/
theorem hasDerivWithinAt_convectiveHeatFlowBUC_zero_fderiv {a : ℝ} (ha : 0 < a)
    (b : E) (v : BUC E F) (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hg : ∀ x, HasFDerivAt v (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) :
    HasDerivWithinAt (fun r ↦ convectiveHeatFlowBUC a r b v)
      (convectiveGeneratorBUC a b g h) (Ici 0) 0 := by
  simpa only [convectiveHeatFlowBUC_zero] using
    BUC.hasDerivWithinAt_zero_of_pointwise (continuous_convectiveHeatFlowBUC_time a b v)
      (continuous_convectiveHeatFlowBUC_time a b (convectiveGeneratorBUC a b g h))
      (fun t ht x ↦ hasDerivAt_convectiveHeatFlow_pointwise_fderiv ha ht b v g h hg hh x)

/-- The complex scalar spatial heat semigroup has the expected generator on BUC² data. -/
theorem complexConvectiveHeatC0Semigroup_hasGeneratorAt_fderiv {a : ℝ} (ha : 0 < a)
    (b : E) (v : BUC E ℂ) (g : BUC E (E →L[ℝ] ℂ)) (h : BUC E (E →L[ℝ] E →L[ℝ] ℂ))
    (hg : ∀ x, HasFDerivAt v (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) :
    (complexConvectiveHeatC0Semigroup a ha.le b).HasGeneratorAt v (convectiveGeneratorBUC a b g h) := by
  apply (hasDerivWithinAt_convectiveHeatFlowBUC_zero_fderiv ha b v g h hg hh).congr
  · intro t ht
    simp only [C0Semigroup.realOrbit, complexConvectiveHeatC0Semigroup_apply, Real.coe_toNNReal _ ht]
  · simp [C0Semigroup.realOrbit]

end

end Planarwave
