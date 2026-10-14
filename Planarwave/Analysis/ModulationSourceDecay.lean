/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.InverseModulationNonlinearity
public import Planarwave.Analysis.ForcedPhaseDerivativeDecay

@[expose] public section

/-!
# The full perturbation source and its decay

Bundle the four terms of `eq:defNtilde`. The profiles `A`, `B`, and `P`
will be `d_perp φ' - Dφ'`, `Dφ'' + (c/2)φ'`, and `φ'`, respectively.
The phase estimates from Step 1 give the `1/(1+t)` bound in Step 3a.
-/

namespace Planarwave

noncomputable section

variable {Y F : Type*} [NormedAddCommGroup Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiply a transverse scalar field by a fixed longitudinal profile. -/
def profileProduct (p : BUC ℝ F) (q : BUC Y ℝ) : BUC (Y × ℝ) F :=
  BUC.smulBUC (transverseLift q) (p.comp Prod.snd uniformContinuous_snd)

@[simp]
theorem profileProduct_apply (p : BUC ℝ F) (q : BUC Y ℝ) (x : Y × ℝ) :
    profileProduct p q x = q x.1 • p x.2 := rfl

theorem norm_profileProduct_le (p : BUC ℝ F) (q : BUC Y ℝ) :
    ‖profileProduct p q‖ ≤ ‖q‖ * ‖p‖ :=
  (BUC.norm_smulBUC_le _ _).trans (mul_le_mul (norm_transverseLift_le q)
    (BUC.norm_comp_le p _ _) (norm_nonneg _) (norm_nonneg q))

/-- Fixed-profile multiplication as a bounded linear map. -/
def profileProductCLM (p : BUC ℝ F) : BUC Y ℝ →L[ℝ] BUC (Y × ℝ) F :=
  LinearMap.mkContinuous
    { toFun := profileProduct p
      map_add' := by intros; ext x; simp [add_smul]
      map_smul' := by intros; ext x; simp [smul_smul] }
    ‖p‖ (fun q ↦ by
      change ‖profileProduct p q‖ ≤ ‖p‖ * ‖q‖
      simpa only [mul_comm] using norm_profileProduct_le p q)

@[simp]
theorem profileProductCLM_apply (p : BUC ℝ F) (q : BUC Y ℝ) :
    profileProductCLM p q = profileProduct p q := rfl

variable [InnerProductSpace ℝ Y]

/-- The full inhomogeneity in the inverse-modulated perturbation equation. -/
def modulationPerturbationSource (A B P : BUC ℝ F) (N : BUC (Y × ℝ) F)
    (s : BUC Y Y) (l g : BUC Y ℝ) : BUC (Y × ℝ) F :=
  profileProduct A l + profileProduct B (phaseGradientSquared s) + N - profileProduct P g

@[simp]
theorem modulationPerturbationSource_apply (A B P : BUC ℝ F) (N : BUC (Y × ℝ) F)
    (s : BUC Y Y) (l g : BUC Y ℝ) (x : Y × ℝ) :
    modulationPerturbationSource A B P N s l g x =
      l x.1 • A x.2 + ‖s x.1‖ ^ 2 • B x.2 + N x - g x.1 • P x.2 := by
  simp only [modulationPerturbationSource, BUC.add_apply, BUC.sub_apply,
    profileProduct_apply, phaseGradientSquared_apply]

/-- Termwise triangle-inequality estimate in `eq:Ntildeest`. -/
theorem norm_modulationPerturbationSource_le (A B P : BUC ℝ F) (N : BUC (Y × ℝ) F)
    (s : BUC Y Y) (l g : BUC Y ℝ) :
    ‖modulationPerturbationSource A B P N s l g‖ ≤
      ‖l‖ * ‖A‖ + ‖s‖ ^ 2 * ‖B‖ + ‖N‖ + ‖g‖ * ‖P‖ := by
  apply (norm_sub_le _ _).trans
  apply add_le_add _ (norm_profileProduct_le P g)
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (norm_add_le _ _).trans
  exact add_le_add (norm_profileProduct_le A l)
    ((norm_profileProduct_le B _).trans
      (mul_le_mul_of_nonneg_right (norm_phaseGradientSquared_le s) (norm_nonneg B)))

/-- Continuity needed for the perturbation Duhamel decomposition. -/
theorem continuousOn_modulationPerturbationSource {I : Set ℝ} (A B P : BUC ℝ F)
    {N : ℝ → BUC (Y × ℝ) F} {s : ℝ → BUC Y Y} {l g : ℝ → BUC Y ℝ}
    (hN : ContinuousOn N I) (hs : ContinuousOn s I)
    (hl : ContinuousOn l I) (hg : ContinuousOn g I) :
    ContinuousOn (fun t ↦ modulationPerturbationSource A B P (N t) (s t) (l t) (g t)) I := by
  have hsq : ContinuousOn (fun t ↦ phaseGradientSquared (s t)) I :=
    (BUC.continuous_bilinearBUC (innerSL ℝ)).comp_continuousOn (hs.prodMk hs)
  exact (((profileProductCLM A).continuous.comp_continuousOn hl).add
    ((profileProductCLM B).continuous.comp_continuousOn hsq)).add hN |>.sub
      ((profileProductCLM P).continuous.comp_continuousOn hg)

/-- The source-decay constant, fixed before the time and fields. -/
def modulationSourceDecayConstant (A B P : BUC ℝ F) (K : ℝ) : ℝ :=
  K * ‖A‖ + K ^ 2 * ‖B‖ + 1 + K * ‖P‖

omit [NormedSpace ℝ F] in
theorem modulationSourceDecayConstant_pos (A B P : BUC ℝ F) {K : ℝ} (hK : 0 ≤ K) :
    0 < modulationSourceDecayConstant A B P K := by
  unfold modulationSourceDecayConstant
  positivity

/-- Decay `5/4` is stronger than decay `1` on nonnegative times. -/
theorem one_add_rpow_neg_five_quarters_le_inv {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ (-(5 : ℝ) / 4) ≤ (1 + t)⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

/-- The full source decays as `1/(1+t)`, using precisely the source,
forcing, gradient, and Laplacian estimates in Steps 1 and 3a. -/
theorem norm_modulationPerturbationSource_decay_le (A B P : BUC ℝ F)
    (N : BUC (Y × ℝ) F) (s : BUC Y Y) (l g : BUC Y ℝ) {K M t : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hM1 : M ≤ 1) (ht : 0 ≤ t)
    (hN : ‖N‖ ≤ M * (1 + t) ^ (-(5 : ℝ) / 4))
    (hs : ‖s‖ ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)))
    (hl : ‖l‖ ≤ K * M * (1 + t) ^ (-(1 : ℝ)))
    (hg : ‖g‖ ≤ K * M * (1 + t) ^ (-(5 : ℝ) / 4)) :
    ‖modulationPerturbationSource A B P N s l g‖ ≤
      modulationSourceDecayConstant A B P K * M / (1 + t) := by
  have hs2 := sq_le_full_decay_of_half_decay (norm_nonneg s) hM hM1 ht hs
  rw [Real.rpow_neg_one] at hl hs2
  have hw := one_add_rpow_neg_five_quarters_le_inv ht
  have hN' : ‖N‖ ≤ M * (1 + t)⁻¹ := hN.trans (mul_le_mul_of_nonneg_left hw hM)
  have hg' : ‖g‖ ≤ K * M * (1 + t)⁻¹ := hg.trans (mul_le_mul_of_nonneg_left hw (mul_nonneg hK hM))
  calc
    _ ≤ ‖l‖ * ‖A‖ + ‖s‖ ^ 2 * ‖B‖ + ‖N‖ + ‖g‖ * ‖P‖ :=
      norm_modulationPerturbationSource_le A B P N s l g
    _ ≤ (K * M * (1 + t)⁻¹) * ‖A‖ + (K ^ 2 * M * (1 + t)⁻¹) * ‖B‖ +
        M * (1 + t)⁻¹ + (K * M * (1 + t)⁻¹) * ‖P‖ := by gcongr
    _ = _ := by unfold modulationSourceDecayConstant; rw [div_eq_mul_inv]; ring

end

end Planarwave
