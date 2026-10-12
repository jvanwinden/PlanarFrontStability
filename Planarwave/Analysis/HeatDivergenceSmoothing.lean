/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional
public import Planarwave.Analysis.BUCNonlinear
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

/-!
# Heat smoothing of a divergence

The exceptional term in Lemma 4.2 is a transverse divergence. Commuting the
derivative through Gaussian averaging bounds its heat evolution by the norm
of the vector field, with no derivative norm on the right hand side.
-/

open scoped InnerProductSpace Gradient Laplacian

namespace Planarwave

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Contraction of a vector field's derivative in an orthonormal basis. -/
def divergenceTraceCLM : (E →L[ℝ] E) →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (innerSL ℝ (stdOrthonormalBasis ℝ E i)).comp
      (ContinuousLinearMap.apply ℝ E (stdOrthonormalBasis ℝ E i))

@[simp]
theorem divergenceTraceCLM_apply (A : E →L[ℝ] E) :
    divergenceTraceCLM A = ∑ i : Fin (Module.finrank ℝ E),
      ⟪stdOrthonormalBasis ℝ E i, A (stdOrthonormalBasis ℝ E i)⟫_ℝ := by
  simp [divergenceTraceCLM]

theorem norm_divergenceTraceCLM_apply_le (A : E →L[ℝ] E) :
    ‖divergenceTraceCLM A‖ ≤ (Module.finrank ℝ E : ℝ) * ‖A‖ := by
  rw [divergenceTraceCLM_apply]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℝ E),
        ‖⟪stdOrthonormalBasis ℝ E i, A (stdOrthonormalBasis ℝ E i)⟫_ℝ‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖stdOrthonormalBasis ℝ E i‖ * ‖A (stdOrthonormalBasis ℝ E i)‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖stdOrthonormalBasis ℝ E i‖ * (‖A‖ * ‖stdOrthonormalBasis ℝ E i‖) := by
          gcongr
          exact A.le_opNorm _
        _ = ‖A‖ := by simp
    _ = _ := by simp

/-- Divergence of a specified BUC derivative field. -/
def divergenceBUC (G : BUC E (E →L[ℝ] E)) : BUC E ℝ :=
  BUC.postcompCLM divergenceTraceCLM G

@[simp]
theorem divergenceBUC_apply (G : BUC E (E →L[ℝ] E)) (x : E) :
    divergenceBUC G x = divergenceTraceCLM (G x) := rfl

theorem norm_divergenceBUC_le (G : BUC E (E →L[ℝ] E)) :
    ‖divergenceBUC G‖ ≤ (Module.finrank ℝ E : ℝ) * ‖G‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  exact (norm_divergenceTraceCLM_apply_le (G x)).trans
    (mul_le_mul_of_nonneg_left (G.norm_apply_le x) (Nat.cast_nonneg _))

/-- Contraction of the rank-one term in the product rule. -/
theorem divergenceTraceCLM_smulRight (l : E →L[ℝ] ℝ) (s : E) :
    divergenceTraceCLM (l.smulRight s) = l s := by
  rw [divergenceTraceCLM_apply]
  calc
    _ = l (∑ i : Fin (Module.finrank ℝ E),
        ⟪stdOrthonormalBasis ℝ E i, s⟫_ℝ • stdOrthonormalBasis ℝ E i) := by
      simp only [ContinuousLinearMap.smulRight_apply, inner_smul_right, map_sum, map_smul,
        smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = l s := by
      simp only [← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr]

/-- The actual BUC derivative field of a scalar times a vector field. -/
def fluxDerivativeBUC (q : BUC E ℝ) (q₁ : BUC E (E →L[ℝ] ℝ))
    (s : BUC E E) (s₁ : BUC E (E →L[ℝ] E)) : BUC E (E →L[ℝ] E) :=
  BUC.smulBUC q s₁ + BUC.bilinearBUC (ContinuousLinearMap.smulRightL ℝ E E) q₁ s

omit [FiniteDimensional ℝ E] in
@[simp]
theorem fluxDerivativeBUC_apply (q : BUC E ℝ) (q₁ : BUC E (E →L[ℝ] ℝ))
    (s : BUC E E) (s₁ : BUC E (E →L[ℝ] E)) (x : E) :
    fluxDerivativeBUC q q₁ s s₁ x = q x • s₁ x + (q₁ x).smulRight (s x) := rfl

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_fluxDerivativeBUC (q : BUC E ℝ) (q₁ : BUC E (E →L[ℝ] ℝ))
    (s : BUC E E) (s₁ : BUC E (E →L[ℝ] E))
    (hq : ∀ x, HasFDerivAt q (q₁ x) x) (hs : ∀ x, HasFDerivAt s (s₁ x) x) (x : E) :
    HasFDerivAt (BUC.smulBUC q s) (fluxDerivativeBUC q q₁ s s₁ x) x :=
  (hq x).smul (hs x)

/-- The divergence product rule, retaining the precise correction sign used
when rewriting the mixed term of Lemma 4.2. -/
theorem divergenceBUC_fluxDerivative (q : BUC E ℝ) (q₁ : BUC E (E →L[ℝ] ℝ))
    (s : BUC E E) (s₁ : BUC E (E →L[ℝ] E)) :
    divergenceBUC (fluxDerivativeBUC q q₁ s s₁) =
      BUC.smulBUC q (divergenceBUC s₁) + BUC.operatorApply q₁ s := by
  ext x
  simp only [divergenceBUC_apply, fluxDerivativeBUC_apply, map_add, map_smul,
    divergenceTraceCLM_smulRight, BUC.add_apply, BUC.smulBUC_apply, BUC.operatorApply_apply]

/-- For an actual phase gradient, the divergence is the challenge's Laplacian. -/
theorem divergenceBUC_gradient (σ : E → ℝ) (s : BUC E E) (s₁ : BUC E (E →L[ℝ] E))
    (hgrad : ∀ y, s y = ∇ σ y) (hs : ∀ y, HasFDerivAt s (s₁ y) y) (x : E) :
    divergenceBUC s₁ x = Δ σ x := by
  have hfun : (fun y ↦ innerSL ℝ (s y)) = fderiv ℝ σ := by
    funext y
    rw [hgrad y]
    exact toDual_gradient
  have hsecond := (innerSL ℝ).hasFDerivAt.comp x (hs x)
  change HasFDerivAt (fun y ↦ innerSL ℝ (s y)) ((innerSL ℝ).comp (s₁ x)) x at hsecond
  rw [hfun] at hsecond
  rw [laplacian_eq_trace_fderiv, hsecond.fderiv, divergenceBUC_apply, divergenceTraceCLM_apply]
  simp only [laplacianTraceCLM, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

variable [MeasurableSpace E] [BorelSpace E]

/-- Heat flow commutes with the divergence of an actual BUC differentiable vector field. -/
theorem heatFlowBUC_divergence {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (F : BUC E E) (G : BUC E (E →L[ℝ] E)) (hG : ∀ x, HasFDerivAt F (G x) x) :
    heatFlowBUC a t (divergenceBUC G) = divergenceBUC (heatFDerivBUC ha ht F) := by
  rw [divergenceBUC, heatFlowBUC_postcomp]
  congr 1
  apply BUC.ext
  intro x
  rw [heatFDerivBUC_apply, fderiv_heatFlow_of_hasFDerivAt a t F G hG]
  rfl

/-- The derivative-free heat-divergence bound used in Lemma 4.2. -/
theorem norm_heatFlowBUC_divergence_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (F : BUC E E) (G : BUC E (E →L[ℝ] E)) (hG : ∀ x, HasFDerivAt F (G x) x) :
    ‖heatFlowBUC a t (divergenceBUC G)‖ ≤
      (Module.finrank ℝ E : ℝ) / heatScale a t * ‖F‖ := by
  rw [heatFlowBUC_divergence ha ht F G hG]
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) * ‖heatFDerivBUC ha ht F‖ := norm_divergenceBUC_le _
    _ ≤ (Module.finrank ℝ E : ℝ) * (‖F‖ / heatScale a t) := by
      gcongr
      exact norm_heatFDerivBUC_le ha ht F
    _ = _ := by ring

/-- For the product flux in Lemma 4.2, only the two undifferentiated factors occur. -/
theorem norm_heatFlowBUC_divergence_smul_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (q : BUC E ℝ) (s : BUC E E) (G : BUC E (E →L[ℝ] E))
    (hG : ∀ x, HasFDerivAt (BUC.smulBUC q s) (G x) x) :
    ‖heatFlowBUC a t (divergenceBUC G)‖ ≤
      ((Module.finrank ℝ E : ℝ) / heatScale a t) * ‖q‖ * ‖s‖ := by
  calc
    _ ≤ ((Module.finrank ℝ E : ℝ) / heatScale a t) * ‖BUC.smulBUC q s‖ :=
      norm_heatFlowBUC_divergence_le ha ht _ G hG
    _ ≤ ((Module.finrank ℝ E : ℝ) / heatScale a t) * (‖q‖ * ‖s‖) :=
      mul_le_mul_of_nonneg_left (BUC.norm_smulBUC_le q s)
        (div_nonneg (Nat.cast_nonneg _) (heatScale_pos_of_pos ha ht).le)
    _ = _ := by ring

end

end Planarwave
