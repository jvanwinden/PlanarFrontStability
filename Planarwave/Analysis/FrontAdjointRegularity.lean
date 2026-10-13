/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontAdjointEstimates
import Planarwave.Analysis.ClassicalODELimit

/-!
# The regular adjoint representative needed in Lemma 4.2

The original spectral hypotheses imply that the supplied L1 weight has an
almost-everywhere equal classical adjoint representative with two integrable
derivatives. We regularize the weak ODE, obtain uniform L1 derivative bounds
by elliptic interpolation, and pass to a classical limit using the integrated
ODE. Fatou's lemma gives integrability of both limiting derivatives.

Only the representative is asserted to be differentiable. Modifying an
integrable weight on a null set cannot affect its spectral pairings.
-/

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

include h₁ h₂ h₃

/-- Adjoint regularity derived from the original hypotheses, with integrable
classical first and second derivatives and the correct adjoint drift sign. -/
theorem exists_frontAdjoint_regularRepresentative :
    ∃ χ : BUC ℝ (ℝ^n), ∃ χ₁ χ₂ : ℝ → ℝ^n,
      ψ =ᵐ[volume] χ ∧ Integrable (χ : ℝ → ℝ^n) ∧ Integrable χ₁ ∧ Integrable χ₂ ∧
      Continuous χ₁ ∧ Continuous χ₂ ∧
      (∀ z, HasDerivAt χ (χ₁ z) z) ∧ (∀ z, HasDerivAt χ₁ (χ₂ z) z) ∧
      (∀ z, D (χ₂ z) - c • χ₁ z + (fderiv ℝ f (φ z)).adjoint (χ z) = 0) := by
  obtain ⟨K, χ, _, _, hχi, hrep, hχlim⟩ :=
    exists_frontAdjoint_lipschitzRepresentative f D c φ ψ h₁ h₂ h₃
  let A := realFrontDerivativeCoefficient f D c φ h₁ h₂
  let R := fun z ↦ (A z).adjoint (χ z)
  have hRcont : Continuous R := by
    have heval : Continuous (fun p : (ℝ^n →L[ℝ] ℝ^n) × ℝ^n ↦ p.1 p.2) := by fun_prop
    exact heval.comp ((ContinuousLinearMap.adjoint.continuous.comp A.continuous).prodMk χ.continuous)
  have hRb (z : ℝ) : ‖R z‖ ≤ ‖A‖ * ‖χ‖ := by
    calc
      _ ≤ ‖(A z).adjoint‖ * ‖χ z‖ := ((A z).adjoint).le_opNorm _
      _ ≤ ‖A‖ * ‖χ‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; gcongr <;> exact BUC.norm_apply_le _ _
  have hq := integrable_frontAdjointReaction f D c φ ψ h₁ h₂ h₃
  have hReq : (fun z ↦ (fderiv ℝ f (φ z)).adjoint (ψ z)) =ᵐ[volume] R := by
    filter_upwards [hrep] with z hz
    change (A z).adjoint (ψ z) = (A z).adjoint (χ z)
    rw [hz]
  have hRi : Integrable R := hq.congr hReq
  let u := fun j ↦ (frontAdjointRegularization f D c φ ψ h₃ j : ℝ → ℝ^n)
  let q := fun j ↦ (frontAdjointReactionRegularization f D c φ ψ h₁ h₂ h₃ j : ℝ → ℝ^n)
  have hqb (j : ℕ) (z : ℝ) : ‖q j z‖ ≤ ‖A‖ * ‖χ‖ := by
    apply norm_longitudinalMollification_le_of_ae_bound hq _ j z
    filter_upwards [hReq] with x hx
    rw [hx]
    exact hRb x
  have hql (z : ℝ) : Tendsto (fun j ↦ q j z) atTop (𝓝 (R z)) := by
    have heq (j : ℕ) : frontAdjointReactionRegularization f D c φ ψ h₁ h₂ h₃ j =
        longitudinalMollification R hRi j := longitudinalMollification_congr_ae hq hRi hReq j
    change Tendsto (fun j ↦ frontAdjointReactionRegularization f D c φ ψ h₁ h₂ h₃ j z) atTop (𝓝 (R z))
    simp_rw [heq]
    exact tendsto_longitudinalMollification_of_continuous hRi hRcont z
  have hu (j : ℕ) : ContDiff ℝ ∞ (u j) := contDiff_longitudinalMollification h₃.integrable j
  have hv (j : ℕ) : ContDiff ℝ ∞ (deriv (u j)) := (contDiff_infty_iff_deriv.mp (hu j)).2
  have hw (j : ℕ) : ContDiff ℝ ∞ (deriv (deriv (u j))) := (contDiff_infty_iff_deriv.mp (hv j)).2
  obtain ⟨C, _, hsup⟩ := exists_frontAdjointRegularization_sup_bound f D c φ ψ h₁ h₂ h₃
  let e : ℝ^n ≃L[ℝ] ℝ^n :=
    (LinearEquiv.ofInjectiveEndo D.toLinearMap h₁.kernel).toContinuousLinearEquiv
  obtain ⟨χ₁, χ₂, hc₁, hc₂, hd₁, hd₂, hODE, k, hk, hl₁, hl₂⟩ :=
    exists_classical_adjointODE_limit e c (fun j ↦ (hv j).continuous)
      (fun j ↦ (hw j).continuous) (fun j ↦ (contDiff_longitudinalMollification hq j).continuous)
      χ.continuous hRcont
      (fun j z ↦ ((hu j).differentiable (by simp) z).hasDerivAt)
      (fun j z ↦ ((hv j).differentiable (by simp) z).hasDerivAt)
      (frontAdjointRegularization_equation f D c φ ψ h₁ h₂ h₃)
      (fun j ↦ (hsup j).2) hqb hχlim hql
  obtain ⟨B, _, hL1⟩ := exists_frontAdjointRegularization_derivative_l1_bound f D c φ ψ h₁ h₂ h₃
  have hbound₁ (j : ℕ) : (∫ z, ‖deriv (u j) z‖) ≤ B * ∫ z, ‖ψ z‖ := by
    have h := hL1 j
    have hn : 0 ≤ ∫ z, ‖deriv (deriv (u j)) z‖ := integral_nonneg fun _ ↦ norm_nonneg _
    change (∫ z, ‖deriv (u j) z‖) + (∫ z, ‖deriv (deriv (u j)) z‖) ≤ _ at h
    linarith
  have hbound₂ (j : ℕ) : (∫ z, ‖deriv (deriv (u j)) z‖) ≤ B * ∫ z, ‖ψ z‖ := by
    have h := hL1 j
    have hn : 0 ≤ ∫ z, ‖deriv (u j) z‖ := integral_nonneg fun _ ↦ norm_nonneg _
    change (∫ z, ‖deriv (u j) z‖) + (∫ z, ‖deriv (deriv (u j)) z‖) ≤ _ at h
    linarith
  have hi₁ : Integrable χ₁ := integrable_of_bounded_integral_norm_of_pointwise
    (fun j ↦ integrable_deriv_longitudinalMollification h₃.integrable (k j)) hc₁
    (fun j ↦ hbound₁ (k j)) hl₁
  have hi₂ : Integrable χ₂ := integrable_of_bounded_integral_norm_of_pointwise
    (fun j ↦ integrable_deriv_deriv_longitudinalMollification h₃.integrable (k j)) hc₂
    (fun j ↦ hbound₂ (k j)) hl₂
  exact ⟨χ, χ₁, χ₂, hrep, hχi, hi₁, hi₂, hc₁, hc₂, hd₁, hd₂, hODE⟩

end

end Planarwave
