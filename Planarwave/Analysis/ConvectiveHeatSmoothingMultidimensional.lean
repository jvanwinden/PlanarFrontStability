/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional

@[expose] public section

/-!
# Quantitative full-dimensional heat smoothing

The Gaussian first derivative estimate, applied on two successive half-time
intervals, gives the inverse-time second derivative bound in the spatial BUC
norm. We also bound the Hessian trace and the diffusion and drift contributions
to the convective generator in terms of the derivative-field norms.
-/

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance : NormedAddCommGroup (BUC E (E →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] F)
local instance : NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] F)) :=
  BUC.instNormedAddCommGroup (α := E) (E := E →L[ℝ] E →L[ℝ] F)

/-- Two successive BUC spatial derivatives with the Gaussian smoothing bounds.
The second derivative is obtained by differentiating each half of the heat orbit. -/
theorem exists_bounded_buc_fderivatives_heatFlow {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    ∃ (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F)),
      (∀ x, HasFDerivAt (heatFlow a t f) (g x) x) ∧
      (∀ x, HasFDerivAt g (h x) x) ∧
      ‖g‖ ≤ ‖f‖ / heatScale a t ∧ ‖h‖ ≤ ‖f‖ / (a * t) := by
  have hhalf : 0 < t / 2 := by positivity
  let v := heatFlowBUC a (t / 2) f
  let g₀ := heatFDerivBUC ha hhalf f
  let g := heatFlowBUC a (t / 2) g₀
  let h := heatFDerivBUC ha hhalf g₀
  have hg₀ : ∀ x, HasFDerivAt v (g₀ x) x :=
    fun x ↦ hasFDerivAt_heatFlow ha hhalf f x
  have hsplit : heatFlow a t f = heatFlow a (t / 2) v := by
    have hcoe : (v : E → F) = heatFlow a (t / 2) f := funext (heatFlowBUC_apply _ _ f)
    rw [hcoe, heatFlow_add_time ha.le hhalf.le hhalf.le f.uniformContinuous
      f.norm_apply_le, add_halves]
  have hg : ∀ x, HasFDerivAt (heatFlow a t f) (g x) x := by
    intro x
    rw [hsplit]
    exact hasFDerivAt_heatFlow_of_hasFDerivAt a (t / 2) v g₀ hg₀ x
  refine ⟨g, h, hg, fun x ↦ hasFDerivAt_heatFlow ha hhalf g₀ x, ?_, ?_⟩
  · apply (BUC.norm_le (div_nonneg (norm_nonneg _) (heatScale_pos_of_pos ha ht).le)).mpr
    intro x
    rw [← (hg x).fderiv]
    exact norm_fderiv_heatFlow_le ha ht f x
  · have hs := heatScale_pos_of_pos ha hhalf
    have hsquare : heatScale a (t / 2) * heatScale a (t / 2) = a * t := by
      nlinarith [heatScale_sq ha.le hhalf.le]
    calc
      ‖h‖ ≤ ‖g₀‖ / heatScale a (t / 2) := norm_heatFDerivBUC_le ha hhalf g₀
      _ ≤ (‖f‖ / heatScale a (t / 2)) / heatScale a (t / 2) :=
        div_le_div_of_nonneg_right (norm_heatFDerivBUC_le ha hhalf f) hs.le
      _ = ‖f‖ / (a * t) := by rw [div_div, hsquare]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- Trace contraction costs at most the spatial dimension in operator norm. -/
theorem norm_laplacianTraceCLM_apply_le (h : E →L[ℝ] E →L[ℝ] F) :
    ‖laplacianTraceCLM h‖ ≤ (Module.finrank ℝ E : ℝ) * ‖h‖ := by
  classical
  simp only [laplacianTraceCLM, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℝ E),
        ‖h (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖h‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖h (stdOrthonormalBasis ℝ E i)‖ * ‖stdOrthonormalBasis ℝ E i‖ :=
          (h (stdOrthonormalBasis ℝ E i)).le_opNorm _
        _ ≤ (‖h‖ * ‖stdOrthonormalBasis ℝ E i‖) * ‖stdOrthonormalBasis ℝ E i‖ :=
          mul_le_mul_of_nonneg_right (h.le_opNorm _) (norm_nonneg _)
        _ = ‖h‖ := by simp
    _ = _ := by simp

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- Separate the diffusion and drift contributions to the spatial BUC generator. -/
theorem norm_convectiveGeneratorBUC_le (a : ℝ) (b : E)
    (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F)) :
    ‖convectiveGeneratorBUC a b g h‖ ≤
      |a| * (Module.finrank ℝ E : ℝ) * ‖h‖ + ‖b‖ * ‖g‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  change ‖a • laplacianTraceCLM (E := E) (F := F) (h x) + g x b‖ ≤ _
  have hhx : ‖h x‖ ≤ ‖h‖ := by
    exact @BUC.norm_apply_le E (E →L[ℝ] E →L[ℝ] F) inferInstance
      ContinuousLinearMap.toNormedAddCommGroup h x
  have htrace : ‖laplacianTraceCLM (E := E) (F := F) (h x)‖ ≤
      (Module.finrank ℝ E : ℝ) * ‖h‖ :=
    (norm_laplacianTraceCLM_apply_le (h x)).trans
      (mul_le_mul_of_nonneg_left hhx (Nat.cast_nonneg _))
  have hgx : ‖g x‖ ≤ ‖g‖ := BUC.norm_apply_le (E := E →L[ℝ] F) g x
  have hdrift : ‖g x b‖ ≤ ‖g‖ * ‖b‖ :=
    ((g x).le_opNorm b).trans (mul_le_mul_of_nonneg_right hgx (norm_nonneg b))
  calc
    _ ≤ ‖a • laplacianTraceCLM (E := E) (F := F) (h x)‖ + ‖g x b‖ := norm_add_le _ _
    _ ≤ |a| * ((Module.finrank ℝ E : ℝ) * ‖h‖) + ‖g‖ * ‖b‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left htrace (abs_nonneg a)) hdrift
    _ = _ := by ring

end

end Planarwave
