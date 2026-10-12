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
norm. Translation preserves both bounds. Taking the trace then gives the
short-time generator estimate for the principal spatial evolution in the paper.
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

/-- The full-dimensional convective heat orbit has BUC derivatives with the same bounds. -/
theorem exists_bounded_buc_fderivatives_convectiveHeatFlow {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) (b : E) (f : BUC E F) :
    ∃ (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F)),
      (∀ x, HasFDerivAt (convectiveHeatFlowBUC a t b f) (g x) x) ∧
      (∀ x, HasFDerivAt g (h x) x) ∧
      ‖g‖ ≤ ‖f‖ / heatScale a t ∧ ‖h‖ ≤ ‖f‖ / (a * t) := by
  obtain ⟨g, h, hg, hh, hgnorm, hhnorm⟩ :=
    exists_bounded_buc_fderivatives_heatFlow ha ht f
  refine ⟨BUC.translate (E := E →L[ℝ] F) (-(t • b)) g,
    BUC.translate (E := E →L[ℝ] E →L[ℝ] F) (-(t • b)) h, ?_, ?_, ?_, ?_⟩
  · intro x
    have hd := (hg (x + t • b)).comp x ((hasFDerivAt_id (𝕜 := ℝ) x).add_const (t • b))
    change HasFDerivAt (fun y ↦ convectiveHeatFlowBUC a t b f y) _ x
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id, convectiveHeatFlowBUC_apply,
      BUC.translate_apply, sub_neg_eq_add] using! hd
  · intro x
    have hd := (hh (x + t • b)).comp x ((hasFDerivAt_id (𝕜 := ℝ) x).add_const (t • b))
    change HasFDerivAt (fun y ↦ BUC.translate (E := E →L[ℝ] F) (-(t • b)) g y) _ x
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id,
      BUC.translate_apply, sub_neg_eq_add] using! hd
  · simpa only [BUC.norm_translate] using hgnorm
  · simpa only [BUC.norm_translate] using hhnorm

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

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- A short-time generator estimate uniform over scalar diffusion rates `a ≥ μ > 0`. -/
theorem time_mul_norm_convectiveGeneratorBUC_le {a μ t : ℝ}
    (hμ : 0 < μ) (hμa : μ ≤ a) (ht : 0 < t) (ht₁ : t ≤ 1)
    (b : E) (f : BUC E F) (g : BUC E (E →L[ℝ] F))
    (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hg : ‖g‖ ≤ ‖f‖ / heatScale a t) (hh : ‖h‖ ≤ ‖f‖ / (a * t)) :
    t * ‖convectiveGeneratorBUC a b g h‖ ≤
      ((Module.finrank ℝ E : ℝ) + ‖b‖ / Real.sqrt (2 * μ)) * ‖f‖ := by
  have ha := hμ.trans_le hμa
  have hs := heatScale_pos_of_pos ha ht
  have hμs : 0 < Real.sqrt (2 * μ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : Real.sqrt (2 * μ) * t ≤ heatScale a t := by
    have heq := heatScale_sq ha.le ht.le
    have hsμ := Real.sq_sqrt (show 0 ≤ 2 * μ by positivity)
    have htt : t * t ≤ t := by nlinarith
    have hm := mul_le_mul_of_nonneg_left htt (show 0 ≤ 2 * μ by positivity)
    have hma := mul_le_mul_of_nonneg_right hμa ht.le
    nlinarith [sq_nonneg (Real.sqrt (2 * μ) * t - heatScale a t)]
  have hfirst : t * ‖g‖ ≤ ‖f‖ / Real.sqrt (2 * μ) := by
    apply (le_div_iff₀ hμs).mpr
    calc
      t * ‖g‖ * Real.sqrt (2 * μ) = ‖g‖ * (Real.sqrt (2 * μ) * t) := by ring
      _ ≤ ‖g‖ * heatScale a t := mul_le_mul_of_nonneg_left hscale (norm_nonneg _)
      _ ≤ ‖f‖ := (le_div_iff₀ hs).mp hg
  have hsecond : t * a * ‖h‖ ≤ ‖f‖ := by
    nlinarith [(le_div_iff₀ (mul_pos ha ht)).mp hh]
  calc
    _ ≤ t * (a * (Module.finrank ℝ E : ℝ) * ‖h‖ + ‖b‖ * ‖g‖) := by
      simpa only [abs_of_pos ha] using
        mul_le_mul_of_nonneg_left (norm_convectiveGeneratorBUC_le a b g h) ht.le
    _ = (Module.finrank ℝ E : ℝ) * (t * a * ‖h‖) + ‖b‖ * (t * ‖g‖) := by ring
    _ ≤ (Module.finrank ℝ E : ℝ) * ‖f‖ + ‖b‖ * (‖f‖ / Real.sqrt (2 * μ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hsecond (by positivity))
        (mul_le_mul_of_nonneg_left hfirst (norm_nonneg _))
    _ = _ := by ring

end

end Planarwave
