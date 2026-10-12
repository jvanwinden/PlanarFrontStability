/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCInterpolation
public import Planarwave.Analysis.LongitudinalOperator
public import Planarwave.Analysis.ClosedOperator

@[expose] public section

/-!
# Closedness and graph norms of the longitudinal differential operator

An invertible diffusion matrix controls the second derivative by the operator, the first
derivative, and the value. BUC interpolation absorbs the first derivative. The resulting
graph-norm estimate proves closedness on the common `BUC²` domain, independently of any
spectral hypothesis. This is the domain-identification step for the semigroups in Section 2.
-/

open Set

namespace Planarwave

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [SMulCommClass ℝ ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- The `BUC²` norm is the maximum of the three jet norms. -/
theorem ComplexBUC2.norm_eq_max (v : ComplexBUC2 V) :
    ‖v‖ = max (max ‖ComplexBUC2.value V v‖ ‖ComplexBUC2.deriv V v‖)
      ‖ComplexBUC2.deriv2 V v‖ := rfl

/-- The elliptic graph-norm estimate, obtained by absorbing the drift using interpolation. -/
theorem exists_longitudinal_graph_bound (D : V →L[ℂ] V) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ x, ‖x‖ ≤ K * ‖D x‖) (c q : ℂ) (A : BUC ℝ (V →L[ℂ] V)) :
    ∃ C > 0, ∀ v : ComplexBUC2 V, ‖v‖ ≤
      C * (‖ComplexBUC2.value V v‖ + ‖longitudinalOperator D c q A v‖) := by
  let d := K * ‖c‖
  let B := K * (‖q‖ * ‖D‖ + ‖BUC.operatorApplyCLM A‖)
  have hd : 0 ≤ d := by positivity
  have hB : 0 ≤ B := by positivity
  let ε : ℝ := 1 / (2 * (d + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : 2 * (d + 1) * ε = 1 := by dsimp [ε]; field_simp
  have hdε : d * ε ≤ 1 / 2 := by nlinarith
  let C₀ := 2 / ε
  let C₂ := 2 * K + 2 * (d * C₀ + B)
  let C₁ := C₀ + ε * C₂
  have hC₀ : 0 ≤ C₀ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨1 + C₁ + C₂, by positivity, ?_⟩
  intro v
  let f := ComplexBUC2.value V v
  let g := ComplexBUC2.deriv V v
  let h := ComplexBUC2.deriv2 V v
  let L := longitudinalOperator D c q A v
  let G := ‖f‖ + ‖L‖
  have hG : 0 ≤ G := by positivity
  have hfG : ‖f‖ ≤ G := le_add_of_nonneg_right (norm_nonneg L)
  have hLG : ‖L‖ ≤ G := le_add_of_nonneg_left (norm_nonneg f)
  have hsecond : ‖h‖ ≤ K * ‖BUC.postcompCLM D h‖ := by
    apply (BUC.norm_le (by positivity)).mpr
    intro x
    exact (hD (h x)).trans
      (mul_le_mul_of_nonneg_left ((BUC.postcompCLM D h).norm_apply_le x) hK)
  have heq : BUC.postcompCLM D h = L + q • BUC.postcompCLM D f - c • g -
      BUC.operatorApplyCLM A f := by
    apply BUC.ext
    intro z
    simp only [L, f, g, h, longitudinalOperator_apply, BUC.postcompCLM_apply,
      BUC.sub_apply, BUC.add_apply, BUC.smul_apply, BUC.operatorApplyCLM_apply,
      BUC.operatorApply_apply, ComplexBUC2.value_apply]
    abel
  have hDnorm : ‖BUC.postcompCLM D h‖ ≤
      ‖L‖ + ‖q‖ * (‖D‖ * ‖f‖) + ‖c‖ * ‖g‖ + ‖BUC.operatorApplyCLM A‖ * ‖f‖ := by
    rw [heq]
    calc
      ‖L + q • BUC.postcompCLM D f - c • g - BUC.operatorApplyCLM A f‖ ≤
          (‖L‖ + ‖q • BUC.postcompCLM D f‖ + ‖c • g‖) + ‖BUC.operatorApplyCLM A f‖ := by
        have h₁ := norm_sub_le (L + q • BUC.postcompCLM D f - c • g)
          (BUC.operatorApplyCLM A f)
        have h₂ := norm_sub_le (L + q • BUC.postcompCLM D f) (c • g)
        have h₃ := norm_add_le L (q • BUC.postcompCLM D f)
        linarith
      _ ≤ ‖L‖ + ‖q‖ * (‖D‖ * ‖f‖) + ‖c‖ * ‖g‖ + ‖BUC.operatorApplyCLM A‖ * ‖f‖ := by
        rw [norm_smul, norm_smul]
        gcongr
        · exact BUC.norm_postcompCLM_apply_le D f
        · exact (BUC.operatorApplyCLM A).le_opNorm f
  have hraw : ‖h‖ ≤ K * ‖L‖ + d * ‖g‖ + B * ‖f‖ := by
    calc
      ‖h‖ ≤ K * ‖BUC.postcompCLM D h‖ := hsecond
      _ ≤ K * (‖L‖ + ‖q‖ * (‖D‖ * ‖f‖) + ‖c‖ * ‖g‖ +
          ‖BUC.operatorApplyCLM A‖ * ‖f‖) := mul_le_mul_of_nonneg_left hDnorm hK
      _ = K * ‖L‖ + d * ‖g‖ + B * ‖f‖ := by dsimp [d, B]; ring
  have hinterp : ‖g‖ ≤ C₀ * ‖f‖ + ε * ‖h‖ :=
    BUC.norm_deriv_le_of_hasDerivAt f g h (ComplexBUC2.hasDerivAt_value V v)
      (ComplexBUC2.hasDerivAt_deriv V v) hε
  have hbound₂ : ‖h‖ ≤ 2 * K * ‖L‖ + 2 * (d * C₀ + B) * ‖f‖ := by
    have hdg := mul_le_mul_of_nonneg_left hinterp hd
    have hdh := mul_le_mul_of_nonneg_right hdε (norm_nonneg h)
    nlinarith
  have h₂G : ‖h‖ ≤ C₂ * G := by
    calc
      ‖h‖ ≤ 2 * K * ‖L‖ + 2 * (d * C₀ + B) * ‖f‖ := hbound₂
      _ ≤ 2 * K * G + 2 * (d * C₀ + B) * G := by gcongr
      _ = C₂ * G := by dsimp [C₂]; ring
  have h₁G : ‖g‖ ≤ C₁ * G := by
    calc
      ‖g‖ ≤ C₀ * ‖f‖ + ε * ‖h‖ := hinterp
      _ ≤ C₀ * G + ε * (C₂ * G) := by gcongr
      _ = C₁ * G := by dsimp [C₁]; ring
  rw [ComplexBUC2.norm_eq_max]
  change max (max ‖f‖ ‖g‖) ‖h‖ ≤ (1 + C₁ + C₂) * G
  apply max_le
  · apply max_le
    · exact hfG.trans (by nlinarith)
    · exact h₁G.trans (by nlinarith)
  · exact h₂G.trans (by nlinarith)

/-- The longitudinal differential expression has a closed graph on `BUC²` whenever diffusion
has a bounded left inverse. No spectral information is used. -/
theorem isClosed_longitudinalOperator_graph (D : V →L[ℂ] V) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ x, ‖x‖ ≤ K * ‖D x‖) (c q : ℂ) (A : BUC ℝ (V →L[ℂ] V)) :
    IsClosed (range ((ComplexBUC2.valueCLM V).prod (longitudinalOperator D c q A))) := by
  obtain ⟨C, hC, hbound⟩ := exists_longitudinal_graph_bound D hK hD c q A
  let T := (ComplexBUC2.valueCLM V).prod (longitudinalOperator D c q A)
  have hanti : AntilipschitzWith (⟨2 * C, by positivity⟩ : NNReal) T := by
    apply T.antilipschitz_of_bound
    intro v
    have hmax₁ : ‖ComplexBUC2.value V v‖ ≤ ‖T v‖ := le_max_left _ _
    have hmax₂ : ‖longitudinalOperator D c q A v‖ ≤ ‖T v‖ := le_max_right _ _
    have hb := hbound v
    change ‖v‖ ≤ (2 * C) * ‖T v‖
    nlinarith
  exact hanti.isClosed_range T.uniformContinuous

end

end Planarwave
