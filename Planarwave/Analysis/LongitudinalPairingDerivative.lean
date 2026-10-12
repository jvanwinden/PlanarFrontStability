/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.LongitudinalPairing
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Transverse differentiation of longitudinal pairings

Differentiate under the adjoint integral with an L1 majorant. The resulting
derivative is itself BUC. This justifies the transverse product rule in the
proof of Lemma 4.2, not merely a formal interchange of derivatives and integrals.
-/

open MeasureTheory Filter Set
open scoped InnerProductSpace

namespace Planarwave

noncomputable section

variable {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem aestronglyMeasurable_pairingDerivativeIntegrand {ψ : ℝ → F}
    (hψ : AEStronglyMeasurable ψ) (g : BUC ℝ (Y →L[ℝ] F)) :
    AEStronglyMeasurable (fun z ↦ (innerSL ℝ (ψ z)).comp (g z)) := by
  have hc : Continuous (fun p : F × (Y →L[ℝ] F) ↦ (innerSL ℝ p.1).comp p.2) := by fun_prop
  exact hc.comp_aestronglyMeasurable (hψ.prodMk g.continuous.aestronglyMeasurable)

theorem norm_pairingDerivativeIntegrand_le (ψ : ℝ → F)
    (g : BUC ℝ (Y →L[ℝ] F)) (z : ℝ) :
    ‖(innerSL ℝ (ψ z)).comp (g z)‖ ≤ ‖ψ z‖ * ‖g‖ := by
  calc
    _ ≤ ‖innerSL ℝ (ψ z)‖ * ‖g z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖ψ z‖ * ‖g‖ := by rw [innerSL_apply_norm]; gcongr; exact g.norm_apply_le z

theorem integrable_pairingDerivativeIntegrand {ψ : ℝ → F} (hψ : Integrable ψ)
    (g : BUC ℝ (Y →L[ℝ] F)) :
    Integrable (fun z ↦ (innerSL ℝ (ψ z)).comp (g z)) :=
  (hψ.norm.mul_const ‖g‖).mono'
    (aestronglyMeasurable_pairingDerivativeIntegrand hψ.aestronglyMeasurable g)
    (ae_of_all _ fun z ↦ norm_pairingDerivativeIntegrand_le ψ g z)

theorem norm_integral_pairingDerivative_le {ψ : ℝ → F} (hψ : Integrable ψ)
    (g : BUC ℝ (Y →L[ℝ] F)) :
    ‖∫ z, (innerSL ℝ (ψ z)).comp (g z)‖ ≤ (∫ z, ‖ψ z‖) * ‖g‖ := by
  calc
    _ ≤ ∫ z, ‖ψ z‖ * ‖g‖ := norm_integral_le_of_norm_le (hψ.norm.mul_const ‖g‖)
      (ae_of_all _ fun z ↦ norm_pairingDerivativeIntegrand_le ψ g z)
    _ = _ := integral_mul_const _ _

/-- The adjoint pairing on transverse-linear-map-valued longitudinal data. -/
def pairingDerivativeCLM (ψ : ℝ → F) (hψ : Integrable ψ) :
    BUC ℝ (Y →L[ℝ] F) →L[ℝ] (Y →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun g : BUC ℝ (Y →L[ℝ] F) ↦ ∫ z, (innerSL ℝ (ψ z)).comp (g z)
      map_add' := by
        intro g h
        simp only [BUC.add_apply, ContinuousLinearMap.comp_add]
        exact integral_add (integrable_pairingDerivativeIntegrand hψ g)
          (integrable_pairingDerivativeIntegrand hψ h)
      map_smul' := by
        intro a g
        simp only [BUC.smul_apply, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply]
        exact integral_smul a _ }
    (∫ z, ‖ψ z‖) (norm_integral_pairingDerivative_le hψ)

/-- A BUC field of candidate transverse derivatives for the longitudinal pairing. -/
def longitudinalPairingDerivative (ψ : ℝ → F) (hψ : Integrable ψ)
    (g : BUC (Y × ℝ) (Y →L[ℝ] F)) : BUC Y (Y →L[ℝ] ℝ) :=
  BUC.postcompCLM (pairingDerivativeCLM ψ hψ) (BUC.curry g)

@[simp]
theorem longitudinalPairingDerivative_apply (ψ : ℝ → F) (hψ : Integrable ψ)
    (g : BUC (Y × ℝ) (Y →L[ℝ] F)) (y : Y) :
    longitudinalPairingDerivative ψ hψ g y =
      ∫ z, (innerSL ℝ (ψ z)).comp (g (y, z)) := rfl

/-- Evaluation can be interchanged with the absolutely convergent operator integral. -/
theorem longitudinalPairingDerivative_apply_vector (ψ : ℝ → F) (hψ : Integrable ψ)
    (g : BUC (Y × ℝ) (Y →L[ℝ] F)) (y s : Y) :
    longitudinalPairingDerivative ψ hψ g y s = ∫ z, ⟪ψ z, g (y, z) s⟫_ℝ :=
  ContinuousLinearMap.integral_apply (integrable_pairingDerivativeIntegrand hψ (BUC.slice g y)) s

theorem norm_longitudinalPairingDerivative_le (ψ : ℝ → F) (hψ : Integrable ψ)
    (g : BUC (Y × ℝ) (Y →L[ℝ] F)) :
    ‖longitudinalPairingDerivative ψ hψ g‖ ≤ (∫ z, ‖ψ z‖) * ‖g‖ := by
  apply (BUC.norm_le (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg g))).mpr
  intro y
  exact (norm_integral_pairingDerivative_le hψ (BUC.slice g y)).trans
    (mul_le_mul_of_nonneg_left (BUC.norm_slice_le g y) (integral_nonneg fun _ ↦ norm_nonneg _))

/-- Differentiation under the longitudinal integral, with an integrable majorant
uniform in the transverse point. -/
theorem hasFDerivAt_longitudinalPairing (ψ : ℝ → F) (hψ : Integrable ψ)
    (v : BUC (Y × ℝ) F) (g : BUC (Y × ℝ) (Y →L[ℝ] F))
    (hg : ∀ y z, HasFDerivAt (fun w ↦ v (w, z)) (g (y, z)) y) (y : Y) :
    HasFDerivAt (longitudinalPairing ψ hψ v) (longitudinalPairingDerivative ψ hψ g y) y := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y z ↦ ⟪ψ z, v (y, z)⟫_ℝ)
    (F' := fun y z ↦ (innerSL ℝ (ψ z)).comp (g (y, z)))
    (bound := fun z ↦ ‖ψ z‖ * ‖g‖) (s := univ) (μ := volume)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun y ↦ (integrable_realPairing hψ (BUC.slice v y)).aestronglyMeasurable)
    (integrable_realPairing hψ (BUC.slice v y))
    (aestronglyMeasurable_pairingDerivativeIntegrand hψ.aestronglyMeasurable (BUC.slice g y))
    (ae_of_all _ fun z y _ ↦ ?_) (hψ.norm.mul_const ‖g‖)
    (ae_of_all _ fun z y _ ↦ (innerSL ℝ (ψ z)).hasFDerivAt.comp y (hg y z))
  exact (norm_pairingDerivativeIntegrand_le ψ (BUC.slice g y) z).trans
    (mul_le_mul_of_nonneg_left (BUC.norm_slice_le g y) (norm_nonneg _))

/-- Evaluating the paired transverse derivative on a transverse vector field
agrees with pairing the evaluated derivative. -/
theorem longitudinalPairing_operatorApply (ψ : ℝ → F) (hψ : Integrable ψ)
    (g : BUC (Y × ℝ) (Y →L[ℝ] F)) (s : BUC Y Y) :
    longitudinalPairing ψ hψ (BUC.operatorApply g (transverseLift s)) =
      BUC.operatorApply (longitudinalPairingDerivative ψ hψ g) s := by
  ext y
  exact (longitudinalPairingDerivative_apply_vector ψ hψ g y (s y)).symm

/-- Integrate by parts in the longitudinal coordinate before taking the
transverse derivative. This avoids any unjustified mixed-derivative interchange. -/
theorem longitudinalPairing_mixedDerivative {ψ ψ₁ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (v vz : BUC (Y × ℝ) F) (vy vyz : BUC (Y × ℝ) (Y →L[ℝ] F))
    (hvz : ∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z)
    (hvy : ∀ y z, HasFDerivAt (fun w ↦ v (w, z)) (vy (y, z)) y)
    (hvyz : ∀ y z, HasFDerivAt (fun w ↦ vz (w, z)) (vyz (y, z)) y) :
    longitudinalPairingDerivative ψ hψ vyz = -longitudinalPairingDerivative ψ₁ hψ₁ vy := by
  apply BUC.ext
  intro y
  have hfirst := hasFDerivAt_longitudinalPairing ψ hψ vz vyz hvyz y
  rw [longitudinalPairing_derivative hψ hψ₁ hderiv v vz hvz] at hfirst
  exact hfirst.unique (hasFDerivAt_longitudinalPairing ψ₁ hψ₁ v vy hvy y).neg

end

end Planarwave
