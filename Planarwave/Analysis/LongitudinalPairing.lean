/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSlices
public import Planarwave.Analysis.BUCPartialDerivatives
public import Planarwave.Analysis.InverseModulationNonlinearity
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

@[expose] public section

/-!
# Longitudinal pairings and integration by parts

The real adjoint pairing in Lemma 4.2 is a bounded operator from spatial BUC
to transverse BUC. Integrable weights and their derivatives allow one or two
longitudinal derivatives to be moved off the perturbation. No decay or
integrability is required of the perturbation itself.

These are general analytic lemmas. Obtaining the regularity of an adjoint
representative from the challenge's spectral hypotheses is a separate step.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

variable {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup Y]

/-- Absolute integrability of an L1 weight paired with bounded data. -/
theorem integrable_realPairing {ψ : ℝ → F} (hψ : Integrable ψ) (v : BUC ℝ F) :
    Integrable (fun z ↦ ⟪ψ z, v z⟫_ℝ) := by
  refine (hψ.norm.mul_const ‖v‖).mono'
    (hψ.aestronglyMeasurable.inner v.continuous.aestronglyMeasurable) ?_
  exact ae_of_all _ fun z ↦ (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (v.norm_apply_le z) (norm_nonneg _))

theorem norm_integral_realPairing_le {ψ : ℝ → F} (hψ : Integrable ψ) (v : BUC ℝ F) :
    ‖∫ z, ⟪ψ z, v z⟫_ℝ‖ ≤ (∫ z, ‖ψ z‖) * ‖v‖ := by
  calc
    _ ≤ ∫ z, ‖ψ z‖ * ‖v‖ := norm_integral_le_of_norm_le (hψ.norm.mul_const ‖v‖)
      (ae_of_all _ fun z ↦ (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (v.norm_apply_le z) (norm_nonneg _)))
    _ = _ := integral_mul_const _ _

/-- The real longitudinal phase functional for an arbitrary integrable weight. -/
def realPairingCLM (ψ : ℝ → F) (hψ : Integrable ψ) : BUC ℝ F →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v ↦ ∫ z, ⟪ψ z, v z⟫_ℝ
      map_add' := by
        intro v w
        simp only [BUC.add_apply, inner_add_right]
        exact integral_add (integrable_realPairing hψ v) (integrable_realPairing hψ w)
      map_smul' := by
        intro a v
        simp only [BUC.smul_apply, inner_smul_right, smul_eq_mul]
        exact integral_const_mul a _ }
    (∫ z, ‖ψ z‖) (norm_integral_realPairing_le hψ)

@[simp]
theorem realPairingCLM_apply (ψ : ℝ → F) (hψ : Integrable ψ) (v : BUC ℝ F) :
    realPairingCLM ψ hψ v = ∫ z, ⟪ψ z, v z⟫_ℝ := rfl

theorem norm_realPairingCLM_le (ψ : ℝ → F) (hψ : Integrable ψ) :
    ‖realPairingCLM ψ hψ‖ ≤ ∫ z, ‖ψ z‖ := by
  apply LinearMap.mkContinuous_norm_le
  exact integral_nonneg fun _ ↦ norm_nonneg _

/-- Pair the longitudinal slices of joint BUC data, retaining transverse BUC. -/
def longitudinalPairing (ψ : ℝ → F) (hψ : Integrable ψ) :
    BUC (Y × ℝ) F →L[ℝ] BUC Y ℝ :=
  (BUC.postcompCLM (realPairingCLM ψ hψ)).comp BUC.curryCLM

@[simp]
theorem longitudinalPairing_apply (ψ : ℝ → F) (hψ : Integrable ψ)
    (v : BUC (Y × ℝ) F) (y : Y) :
    longitudinalPairing ψ hψ v y = ∫ z, ⟪ψ z, v (y, z)⟫_ℝ := rfl

/-- The pairing depends only on the almost-everywhere class of its weight.
Thus a smooth adjoint representative suffices, even if the supplied weight
has been changed on a null set. -/
theorem longitudinalPairing_congr_ae {ψ χ : ℝ → F} (hψ : Integrable ψ) (hχ : Integrable χ)
    (h : ψ =ᵐ[volume] χ) : longitudinalPairing (Y := Y) ψ hψ = longitudinalPairing χ hχ := by
  ext v y
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]

theorem norm_longitudinalPairing_le (ψ : ℝ → F) (hψ : Integrable ψ)
    (v : BUC (Y × ℝ) F) :
    ‖longitudinalPairing ψ hψ v‖ ≤ (∫ z, ‖ψ z‖) * ‖v‖ := by
  apply (BUC.norm_le (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg v))).mpr
  intro y
  exact (norm_integral_realPairing_le hψ (BUC.slice v y)).trans
    (mul_le_mul_of_nonneg_left (BUC.norm_slice_le v y) (integral_nonneg fun _ ↦ norm_nonneg _))

/-- A transverse scalar factor can be pulled outside the longitudinal pairing. -/
theorem longitudinalPairing_smul (ψ : ℝ → F) (hψ : Integrable ψ)
    (q : BUC Y ℝ) (v : BUC (Y × ℝ) F) :
    longitudinalPairing ψ hψ (BUC.smulBUC (transverseLift q) v) =
      BUC.smulBUC q (longitudinalPairing ψ hψ v) := by
  ext y
  simp only [longitudinalPairing_apply, BUC.smulBUC_apply, transverseLift_apply,
    inner_smul_right, smul_eq_mul]
  exact integral_const_mul _ _

/-- Integration by parts on the whole line. Integrability of the product
and its derivative supplies the vanishing boundary terms. -/
theorem realPairingCLM_derivative {ψ ψ₁ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (v v₁ : BUC ℝ F) (hv : ∀ z, HasDerivAt v (v₁ z) z) :
    realPairingCLM ψ hψ v₁ = -realPairingCLM ψ₁ hψ₁ v := by
  exact integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L := innerSL ℝ)
    (fun z _ ↦ hderiv z) (fun z _ ↦ hv z)
    (integrable_realPairing hψ v₁) (integrable_realPairing hψ₁ v)
    (integrable_realPairing hψ v)

/-- Two integrations by parts transfer both derivatives to the integrable weight. -/
theorem realPairingCLM_secondDerivative {ψ ψ₁ ψ₂ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁) (hψ₂ : Integrable ψ₂)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (hderiv₁ : ∀ z, HasDerivAt ψ₁ (ψ₂ z) z)
    (v v₁ v₂ : BUC ℝ F) (hv : ∀ z, HasDerivAt v (v₁ z) z)
    (hv₁ : ∀ z, HasDerivAt v₁ (v₂ z) z) :
    realPairingCLM ψ hψ v₂ = realPairingCLM ψ₂ hψ₂ v := by
  rw [realPairingCLM_derivative hψ hψ₁ hderiv v₁ v₂ hv₁,
    realPairingCLM_derivative hψ₁ hψ₂ hderiv₁ v v₁ hv, neg_neg]

/-- The first integration by parts as an equality of transverse BUC fields. -/
theorem longitudinalPairing_derivative {ψ ψ₁ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (v vz : BUC (Y × ℝ) F)
    (hv : ∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z) :
    longitudinalPairing ψ hψ vz = -longitudinalPairing ψ₁ hψ₁ v := by
  ext y
  exact realPairingCLM_derivative hψ hψ₁ hderiv (BUC.slice v y) (BUC.slice vz y) (hv y)

/-- The second integration by parts as an equality of transverse BUC fields. -/
theorem longitudinalPairing_secondDerivative {ψ ψ₁ ψ₂ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁) (hψ₂ : Integrable ψ₂)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (hderiv₁ : ∀ z, HasDerivAt ψ₁ (ψ₂ z) z)
    (v vz vzz : BUC (Y × ℝ) F)
    (hv : ∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z)
    (hvz : ∀ y z, HasDerivAt (fun r ↦ vz (y, r)) (vzz (y, z)) z) :
    longitudinalPairing ψ hψ vzz = longitudinalPairing ψ₂ hψ₂ v := by
  ext y
  exact realPairingCLM_secondDerivative hψ hψ₁ hψ₂ hderiv hderiv₁
    (BUC.slice v y) (BUC.slice vz y) (BUC.slice vzz y) (hv y) (hvz y)

/-- Pairing a longitudinal derivative costs only the undifferentiated perturbation norm. -/
theorem norm_longitudinalPairing_derivative_le {ψ ψ₁ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (v vz : BUC (Y × ℝ) F)
    (hv : ∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z) :
    ‖longitudinalPairing ψ hψ vz‖ ≤ (∫ z, ‖ψ₁ z‖) * ‖v‖ := by
  rw [longitudinalPairing_derivative hψ hψ₁ hderiv v vz hv, norm_neg]
  exact norm_longitudinalPairing_le ψ₁ hψ₁ v

/-- Pairing a second longitudinal derivative also loses no perturbation derivatives. -/
theorem norm_longitudinalPairing_secondDerivative_le {ψ ψ₁ ψ₂ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁) (hψ₂ : Integrable ψ₂)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (hderiv₁ : ∀ z, HasDerivAt ψ₁ (ψ₂ z) z)
    (v vz vzz : BUC (Y × ℝ) F)
    (hv : ∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z)
    (hvz : ∀ y z, HasDerivAt (fun r ↦ vz (y, r)) (vzz (y, z)) z) :
    ‖longitudinalPairing ψ hψ vzz‖ ≤ (∫ z, ‖ψ₂ z‖) * ‖v‖ := by
  rw [longitudinalPairing_secondDerivative hψ hψ₁ hψ₂ hderiv hderiv₁ v vz vzz hv hvz]
  exact norm_longitudinalPairing_le ψ₂ hψ₂ v

end

end Planarwave
