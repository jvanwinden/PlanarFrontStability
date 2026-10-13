/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.LinearCutoffJet
public import Planarwave.Analysis.LongitudinalPairing
public import Planarwave.Analysis.BUCBilinear

@[expose] public section

/-!
# Pairing the scaling variation

The scaling argument in Lemma `lem:ndispersion` uses the variation
`-z • φ'(z)`. Expanding compact cutoffs justify its adjoint pairing
without assuming that the unbounded linear factor itself belongs to BUC.
-/

open Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Dominated convergence for the two terms of a cutoff scaling commutator. -/
theorem tendsto_realPairing_cutoff_commutator (ψ : ℝ → F) (hψ : Integrable ψ)
    (q r : BUC ℝ F) (η₁ η₂ : ℕ → BUC ℝ ℝ) (C₁ C₂ : ℝ)
    (hb : ∀ k z, ‖η₁ k z‖ ≤ C₁ ∧ ‖η₂ k z‖ ≤ C₂)
    (hl : ∀ z, Tendsto (fun k ↦ η₁ k z) atTop (𝓝 1) ∧
      Tendsto (fun k ↦ η₂ k z) atTop (𝓝 0)) :
    Tendsto (fun k ↦ realPairingCLM ψ hψ
      (BUC.smulBUC (η₁ k) q + BUC.smulBUC (η₂ k) r)) atTop
      (𝓝 (realPairingCLM ψ hψ q)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z ↦ ‖ψ z‖ * (C₁ * ‖q‖ + C₂ * ‖r‖))
  · exact Eventually.of_forall fun k ↦
      (integrable_realPairing hψ (BUC.smulBUC (η₁ k) q + BUC.smulBUC (η₂ k) r)).aestronglyMeasurable
  · exact Eventually.of_forall fun k ↦ ae_of_all _ fun z ↦ by
      change ‖⟪ψ z, η₁ k z • q z + η₂ k z • r z⟫_ℝ‖ ≤ _
      apply (norm_inner_le_norm _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_add_le _ _).trans
      simp only [norm_smul]
      exact add_le_add
        (mul_le_mul (hb k z).1 (q.norm_apply_le z) (norm_nonneg _) ((norm_nonneg _).trans (hb k z).1))
        (mul_le_mul (hb k z).2 (r.norm_apply_le z) (norm_nonneg _) ((norm_nonneg _).trans (hb k z).2))
  · exact hψ.norm.mul_const _
  · exact ae_of_all _ fun z ↦ by
      have hq : Tendsto (fun k ↦ η₁ k z • q z) atTop (𝓝 ((1 : ℝ) • q z)) :=
        (hl z).1.smul tendsto_const_nhds
      have hr : Tendsto (fun k ↦ η₂ k z • r z) atTop (𝓝 ((0 : ℝ) • r z)) :=
        (hl z).2.smul tendsto_const_nhds
      simpa only [BUC.add_apply, BUC.smulBUC_apply, one_smul, zero_smul, add_zero] using!
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ψ z) atTop (𝓝 (ψ z))).inner (hq.add hr)

/-- The adjoint pairing of `2 D p' + c p` vanishes when `p` is a kernel
mode. This is the equation for the paper's scaling variation, justified
by compactly supported approximations of its linear factor. -/
theorem realPairing_scaling_commutator_eq_zero
    (ψ : ℝ → F) (hψ : Integrable ψ) (D : F →L[ℝ] F) (c : ℝ)
    (A : BUC ℝ (F →L[ℝ] F)) (p p₁ p₂ : BUC ℝ F)
    (hp : ∀ z, HasDerivAt p (p₁ z) z) (hp₁ : ∀ z, HasDerivAt p₁ (p₂ z) z)
    (hker : ∀ z, D (p₂ z) + c • p₁ z + A z (p z) = 0)
    (hadj : ∀ (v v₁ v₂ : BUC ℝ F), (∀ z, HasDerivAt v (v₁ z) z) →
      (∀ z, HasDerivAt v₁ (v₂ z) z) →
      realPairingCLM ψ hψ (BUC.postcompCLM D v₂ + c • v₁ + BUC.operatorApply A v) = 0) :
    realPairingCLM ψ hψ ((2 : ℝ) • BUC.postcompCLM D p₁ + c • p) = 0 := by
  obtain ⟨η, η₁, η₂, C₁, C₂, _, _, hd, hb, hl⟩ := exists_bounded_linear_cutoff_jets
  let q := (2 : ℝ) • BUC.postcompCLM D p₁ + c • p
  let r := BUC.postcompCLM D p
  have heq (k : ℕ) : realPairingCLM ψ hψ
      (BUC.smulBUC (η₁ k) q + BUC.smulBUC (η₂ k) r) = 0 := by
    let v := BUC.smulBUC (η k) p
    let v₁ := BUC.smulBUC (η₁ k) p + BUC.smulBUC (η k) p₁
    let v₂ := BUC.smulBUC (η₂ k) p + (2 : ℝ) • BUC.smulBUC (η₁ k) p₁ +
      BUC.smulBUC (η k) p₂
    have hv (z : ℝ) : HasDerivAt v (v₁ z) z := by
      simpa only [v, v₁, BUC.add_apply, BUC.smulBUC_apply, add_comm] using! (hd k z).1.smul (hp z)
    have hv₁ (z : ℝ) : HasDerivAt v₁ (v₂ z) z := by
      convert! ((hd k z).2.smul (hp z)).add ((hd k z).1.smul (hp₁ z)) using 1
      simp only [v₂, BUC.add_apply, BUC.smulBUC_apply, BUC.smul_apply]
      module
    have hop : BUC.postcompCLM D v₂ + c • v₁ + BUC.operatorApply A v =
        BUC.smulBUC (η₁ k) q + BUC.smulBUC (η₂ k) r := by
      ext z
      change D (η₂ k z • p z + (2 : ℝ) • (η₁ k z • p₁ z) + η k z • p₂ z) +
        c • (η₁ k z • p z + η k z • p₁ z) + A z (η k z • p z) =
          η₁ k z • ((2 : ℝ) • D (p₁ z) + c • p z) + η₂ k z • D (p z)
      have hz := congrArg (fun x : F ↦ η k z • x) (hker z)
      simp only [smul_add, smul_zero] at hz
      simp only [map_add, map_smul, smul_add]
      calc
        _ = η₁ k z • ((2 : ℝ) • D (p₁ z) + c • p z) + η₂ k z • D (p z) +
            (η k z • D (p₂ z) + η k z • (c • p₁ z) + η k z • A z (p z)) := by module
        _ = _ := by rw [hz, add_zero]; simp only [smul_add]
    rw [← hop]
    exact hadj v v₁ v₂ hv hv₁
  exact tendsto_nhds_unique (tendsto_realPairing_cutoff_commutator ψ hψ q r η₁ η₂ C₁ C₂ hb hl)
    (by simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)))

end

end Planarwave
