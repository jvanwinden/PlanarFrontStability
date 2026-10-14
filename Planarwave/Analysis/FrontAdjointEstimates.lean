/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAdjointRegularization
import Planarwave.Analysis.L1EllipticEstimate
import Planarwave.Analysis.L1DerivativeBoundedness
import Planarwave.Analysis.LipschitzAELimit

/-!
# Uniform derivative estimates for adjoint regularizations

The original diffusion is invertible. Applying the L1 elliptic estimate to
the exact regularized adjoint ODE gives first- and second-derivative bounds
independent of the smoothing index. The source estimate uses the actual
bounded coefficient `f'(φ)`; no extra regularity of `ψ` is assumed.
-/

open MeasureTheory Filter
open scoped ContDiff Topology NNReal

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₁ h₂ h₃

/-- Uniform L1 bounds for the actual adjoint regularizations' first two derivatives. -/
theorem exists_frontAdjointRegularization_derivative_l1_bound :
    ∃ C > 0, ∀ j,
      (∫ z, ‖deriv (frontAdjointRegularization f D c φ ψ h₃ j) z‖) +
        (∫ z, ‖deriv (deriv (frontAdjointRegularization f D c φ ψ h₃ j)) z‖) ≤
      C * ∫ z, ‖ψ z‖ := by
  let e : ℝ^n ≃L[ℝ] ℝ^n :=
    (LinearEquiv.ofInjectiveEndo D.toLinearMap h₁.kernel).toContinuousLinearEquiv
  have hD (a : ℝ^n) : ‖a‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖D a‖ := by
    calc
      _ = ‖e.symm (e a)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e a‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ = _ := rfl
  obtain ⟨C, hC, hb⟩ := exists_l1_adjointODE_derivative_bound D
    (norm_nonneg e.symm.toContinuousLinearMap) hD c
  let A := realFrontDerivativeCoefficient f D c φ h₁ h₂
  refine ⟨C * (1 + ‖A‖), by positivity, fun j ↦ ?_⟩
  let u := frontAdjointRegularization f D c φ ψ h₃ j
  let q := frontAdjointReactionRegularization f D c φ ψ h₁ h₂ h₃ j
  have hu : ContDiff ℝ ∞ (u : ℝ → ℝ^n) :=
    contDiff_longitudinalMollification h₃.integrable j
  have hv := (contDiff_infty_iff_deriv.mp hu).2
  have hw := (contDiff_infty_iff_deriv.mp hv).2
  have hq := integrable_frontAdjointReaction f D c φ ψ h₁ h₂ h₃
  have hbound := hb u (deriv u) (deriv (deriv u)) q hv.continuous hw.continuous
    (fun z ↦ (hu.differentiable (by simp) z).hasDerivAt)
    (fun z ↦ (hv.differentiable (by simp) z).hasDerivAt)
    (integrable_longitudinalMollification h₃.integrable j)
    (integrable_deriv_longitudinalMollification h₃.integrable j)
    (integrable_deriv_deriv_longitudinalMollification h₃.integrable j)
    (integrable_longitudinalMollification hq j)
    (frontAdjointRegularization_equation f D c φ ψ h₁ h₂ h₃ j)
  have hmass : (∫ z, ‖u z‖) ≤ ∫ z, ‖ψ z‖ :=
    integral_norm_longitudinalMollification_le h₃.integrable j
  have hsource : (∫ z, ‖q z‖) ≤ ‖A‖ * ∫ z, ‖ψ z‖ :=
    (integral_norm_longitudinalMollification_le hq j).trans
      (integral_norm_frontAdjointReaction_le f D c φ ψ h₁ h₂ h₃)
  calc
    _ ≤ C * ((∫ z, ‖u z‖) + ∫ z, ‖q z‖) := hbound
    _ ≤ C * ((∫ z, ‖ψ z‖) + ‖A‖ * ∫ z, ‖ψ z‖) := by gcongr
    _ = _ := by ring

/-- Uniform supremum bounds follow from the L1 derivative bounds and the zero
limits at infinity. -/
theorem exists_frontAdjointRegularization_sup_bound :
    ∃ C > 0, ∀ j,
      ‖frontAdjointRegularization f D c φ ψ h₃ j‖ ≤ C * (∫ z, ‖ψ z‖) ∧
      ∀ z, ‖deriv (frontAdjointRegularization f D c φ ψ h₃ j) z‖ ≤ C * ∫ z, ‖ψ z‖ := by
  obtain ⟨C, hC, hb⟩ := exists_frontAdjointRegularization_derivative_l1_bound f D c φ ψ h₁ h₂ h₃
  refine ⟨C, hC, fun j ↦ ?_⟩
  let u := frontAdjointRegularization f D c φ ψ h₃ j
  have hu : ContDiff ℝ ∞ (u : ℝ → ℝ^n) := contDiff_longitudinalMollification h₃.integrable j
  have hv := (contDiff_infty_iff_deriv.mp hu).2
  have hi : Integrable (u : ℝ → ℝ^n) := integrable_longitudinalMollification h₃.integrable j
  have hvi : Integrable (deriv u) := integrable_deriv_longitudinalMollification h₃.integrable j
  have hwi : Integrable (deriv (deriv u)) := integrable_deriv_deriv_longitudinalMollification h₃.integrable j
  have hV : 0 ≤ ∫ z, ‖deriv u z‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have hW : 0 ≤ ∫ z, ‖deriv (deriv u) z‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have hsum := hb j
  change (∫ z, ‖deriv u z‖) + (∫ z, ‖deriv (deriv u) z‖) ≤ C * (∫ z, ‖ψ z‖) at hsum
  constructor
  · exact (buc_norm_le_integral_norm_derivative u hi hvi
      (fun z ↦ (hu.differentiable (by simp) z).hasDerivAt)).trans (by linarith)
  · intro z
    exact (norm_le_integral_norm_derivative hvi hwi
      (fun z ↦ (hv.differentiable (by simp) z).hasDerivAt) z).trans (by linarith)

/-- The original measurable adjoint has a bounded Lipschitz representative.
Every regularization converges to this representative at every point. This
does not yet assert that the representative has two classical derivatives. -/
theorem exists_frontAdjoint_lipschitzRepresentative :
    ∃ K : ℝ≥0, ∃ χ : BUC ℝ (ℝ^n),
      LipschitzWith K χ ∧ ‖χ‖ ≤ K ∧ Integrable (χ : ℝ → ℝ^n) ∧
      ψ =ᵐ[volume] χ ∧
      ∀ z, Tendsto (fun j ↦ frontAdjointRegularization f D c φ ψ h₃ j z) atTop (𝓝 (χ z)) := by
  obtain ⟨C, hC, hb⟩ := exists_frontAdjointRegularization_sup_bound f D c φ ψ h₁ h₂ h₃
  let K : ℝ≥0 := ⟨C * (∫ z, ‖ψ z‖), mul_nonneg hC.le (integral_nonneg fun _ ↦ norm_nonneg _)⟩
  have hLip (j : ℕ) : LipschitzWith K (frontAdjointRegularization f D c φ ψ h₃ j) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      ((contDiff_longitudinalMollification h₃.integrable j).differentiable (by simp))
    intro z
    exact_mod_cast (hb j).2 z
  obtain ⟨χ, hχLip, hrep, hlim⟩ := exists_lipschitz_representative_of_ae_tendsto hLip
    (ae_tendsto_longitudinalMollification h₃.integrable)
  have hχbound (z : ℝ) : ‖χ z‖ ≤ K :=
    le_of_tendsto (hlim z).norm (Filter.Eventually.of_forall fun j ↦
      ((frontAdjointRegularization f D c φ ψ h₃ j).norm_apply_le z).trans (hb j).1)
  let χb : BUC ℝ (ℝ^n) :=
    ⟨BoundedContinuousFunction.ofNormedAddCommGroup χ hχLip.continuous K hχbound,
      hχLip.uniformContinuous⟩
  exact ⟨K, χb, hχLip, (BUC.norm_le K.coe_nonneg).mpr hχbound,
    h₃.integrable.congr hrep, hrep, hlim⟩

end

end Planarwave
