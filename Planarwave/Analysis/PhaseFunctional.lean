/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Planarwave.Challenge
import Planarwave.Analysis.BUC

/-!
# The phase functional

This file bundles the complex phase functional used in the spectral decomposition in the cited
paper.  For an integrable real adjoint eigenfunction `ψ`, it is

`v ↦ ∫ z, ⟪embed (ψ z), v z⟫_ℂ`.

The domain is the space of complex-valued bounded uniformly continuous longitudinal functions.
-/

open scoped InnerProductSpace
open MeasureTheory

noncomputable section

namespace Planarwave

variable {n : ℕ}

/-- The real-to-complex embedding used in `Challenge` preserves the Euclidean norm. -/
theorem norm_embed (x : EuclideanSpace ℝ (Fin n)) : ‖embed x‖ = ‖x‖ := by
  simp [embed, EuclideanSpace.norm_eq]

/-- The real Euclidean inner product is preserved by the real-to-complex embedding. -/
theorem inner_embed (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪embed x, embed y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) := by
  simp [embed, PiLp.inner_apply, RCLike.inner_apply]

/-- The real-to-complex Euclidean embedding is continuous. -/
theorem continuous_embed :
    Continuous (embed : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) := by
  unfold embed
  fun_prop

/-- The longitudinal phase space appearing in the paper. -/
abbrev LongitudinalBUC (n : ℕ) := BUC ℝ (EuclideanSpace ℂ (Fin n))

/-- The pointwise integrand defining the phase functional. -/
noncomputable def phaseIntegrand (ψ : ℝ → EuclideanSpace ℝ (Fin n))
    (v : LongitudinalBUC n) (z : ℝ) : ℂ :=
  ⟪embed (ψ z), v z⟫_ℂ

/-- The pointwise integrand is strongly measurable whenever the adjoint eigenfunction is. -/
theorem phaseIntegrand_aestronglyMeasurable
    {ψ : ℝ → EuclideanSpace ℝ (Fin n)} (hψ : AEStronglyMeasurable ψ)
    (v : LongitudinalBUC n) : AEStronglyMeasurable (phaseIntegrand ψ v) := by
  exact (continuous_embed.comp_aestronglyMeasurable hψ).inner
    v.continuous.aestronglyMeasurable

/-- Pointwise domination by the `L¹` weight of the adjoint eigenfunction and the BUC norm. -/
theorem norm_phaseIntegrand_le (ψ : ℝ → EuclideanSpace ℝ (Fin n))
    (v : LongitudinalBUC n) (z : ℝ) :
    ‖phaseIntegrand ψ v z‖ ≤ ‖ψ z‖ * ‖v‖ := by
  calc
    ‖phaseIntegrand ψ v z‖ ≤ ‖embed (ψ z)‖ * ‖v z‖ := norm_inner_le_norm _ _
    _ = ‖ψ z‖ * ‖v z‖ := by rw [norm_embed]
    _ ≤ ‖ψ z‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_left (BUC.norm_apply_le v z) (norm_nonneg _)

/-- The paper's phase integrand is Bochner integrable. -/
theorem integrable_phaseIntegrand
    {ψ : ℝ → EuclideanSpace ℝ (Fin n)} (hψ : Integrable ψ)
    (v : LongitudinalBUC n) : Integrable (phaseIntegrand ψ v) := by
  exact (hψ.norm.mul_const ‖v‖).mono'
    (phaseIntegrand_aestronglyMeasurable hψ.aestronglyMeasurable v)
    (ae_of_all _ fun z ↦ norm_phaseIntegrand_le ψ v z)

/-- The unbundled phase integral. -/
noncomputable def phaseIntegral (ψ : ℝ → EuclideanSpace ℝ (Fin n))
    (v : LongitudinalBUC n) : ℂ :=
  ∫ z, phaseIntegrand ψ v z

/-- The phase integral is additive in its BUC argument. -/
theorem phaseIntegral_add
    {ψ : ℝ → EuclideanSpace ℝ (Fin n)} (hψ : Integrable ψ)
    (v w : LongitudinalBUC n) :
    phaseIntegral ψ (v + w) = phaseIntegral ψ v + phaseIntegral ψ w := by
  rw [phaseIntegral, phaseIntegral, phaseIntegral]
  simp only [phaseIntegrand, BUC.add_apply, inner_add_right]
  exact integral_add (integrable_phaseIntegrand hψ v) (integrable_phaseIntegrand hψ w)

/-- The phase integral is complex-linear in its BUC argument. -/
theorem phaseIntegral_smul
    (ψ : ℝ → EuclideanSpace ℝ (Fin n)) (a : ℂ) (v : LongitudinalBUC n) :
    phaseIntegral ψ (a • v) = a • phaseIntegral ψ v := by
  simp only [phaseIntegral, phaseIntegrand, BUC.smul_apply, inner_smul_right, smul_eq_mul]
  exact integral_const_mul a _

/-- The phase integral has exactly the norm bound used in the paper. -/
theorem norm_phaseIntegral_le
    {ψ : ℝ → EuclideanSpace ℝ (Fin n)} (hψ : Integrable ψ)
    (v : LongitudinalBUC n) :
    ‖phaseIntegral ψ v‖ ≤ (∫ z, ‖ψ z‖) * ‖v‖ := by
  calc
    ‖phaseIntegral ψ v‖ ≤ ∫ z, ‖ψ z‖ * ‖v‖ :=
      norm_integral_le_of_norm_le (hψ.norm.mul_const ‖v‖)
        (ae_of_all _ fun z ↦ norm_phaseIntegrand_le ψ v z)
    _ = (∫ z, ‖ψ z‖) * ‖v‖ := integral_mul_const _ _

/-- The phase integral as a complex linear map. -/
noncomputable def phaseLinearMap
    (ψ : ℝ → EuclideanSpace ℝ (Fin n)) (hψ : Integrable ψ) :
    LongitudinalBUC n →ₗ[ℂ] ℂ where
  toFun := phaseIntegral ψ
  map_add' := phaseIntegral_add hψ
  map_smul' := phaseIntegral_smul ψ

/-- The phase functional `ℓ` from the paper, bundled as a continuous complex-linear map. -/
noncomputable def phaseFunctional
    (ψ : ℝ → EuclideanSpace ℝ (Fin n)) (hψ : Integrable ψ) :
    LongitudinalBUC n →L[ℂ] ℂ :=
  (phaseLinearMap ψ hψ).mkContinuous (∫ z, ‖ψ z‖) (norm_phaseIntegral_le hψ)

@[simp]
theorem phaseFunctional_apply
    (ψ : ℝ → EuclideanSpace ℝ (Fin n)) (hψ : Integrable ψ)
    (v : LongitudinalBUC n) :
    phaseFunctional ψ hψ v = ∫ z, ⟪embed (ψ z), v z⟫_ℂ :=
  rfl

/-- The operator norm is bounded by the `L¹` norm of the adjoint eigenfunction. -/
theorem norm_phaseFunctional_le
    (ψ : ℝ → EuclideanSpace ℝ (Fin n)) (hψ : Integrable ψ) :
    ‖phaseFunctional ψ hψ‖ ≤ ∫ z, ‖ψ z‖ := by
  apply LinearMap.mkContinuous_norm_le
  exact integral_nonneg fun _ ↦ norm_nonneg _

/-- Challenge's normalization says that the phase functional evaluates to one on the embedded
translation mode.  The BUC representative is supplied explicitly because `Challenge` states
bounded uniform continuity separately from the bare function `z ↦ embed (deriv φ z)`. -/
theorem phaseFunctional_embedded_deriv_eq_one
    (φ ψ : ℝ → EuclideanSpace ℝ (Fin n)) (hψ : Integrable ψ)
    (hnormalized : ∫ z, ⟪ψ z, deriv φ z⟫_ℝ = 1)
    (translationMode : LongitudinalBUC n)
    (htranslationMode : ∀ z, translationMode z = embed (deriv φ z)) :
    phaseFunctional ψ hψ translationMode = 1 := by
  rw [phaseFunctional_apply]
  calc
    (∫ z, ⟪embed (ψ z), translationMode z⟫_ℂ) =
        ∫ z, (⟪ψ z, deriv φ z⟫_ℝ : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [htranslationMode z, inner_embed]
    _ = ((∫ z, ⟪ψ z, deriv φ z⟫_ℝ : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [hnormalized]; norm_num

/-- The preceding normalization result specialized directly to the spectral-stability hypothesis
from `Challenge`. -/
theorem phaseFunctional_embedded_deriv_eq_one_of_spectralStability
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {c : ℝ} {φ ψ : ℝ → EuclideanSpace ℝ (Fin n)}
    (hstable : IsSpectrallyStableWithAdjoint f D c φ ψ)
    (translationMode : LongitudinalBUC n)
    (htranslationMode : ∀ z, translationMode z = embed (deriv φ z)) :
    phaseFunctional ψ hstable.integrable translationMode = 1 :=
  phaseFunctional_embedded_deriv_eq_one φ ψ hstable.integrable hstable.normalized
    translationMode htranslationMode

end Planarwave
