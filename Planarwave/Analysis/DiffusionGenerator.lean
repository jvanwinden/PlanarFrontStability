/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionSemigroup
import all Planarwave.Analysis.DiffusionEigenbasis
import all Planarwave.Analysis.FrontCoefficient
import Planarwave.Analysis.LongitudinalClosedness

/-!
# Exact domain of the principal longitudinal generator

The positive diffusion eigenvalues make the complexified diffusion invertible. The elliptic
graph-norm estimate therefore closes the differential-operator graph on `BUC²`. Combining this
with the heat-regularization core result identifies the full generator domain, not just its
action on smooth functions. This completes the principal-generator identification in Lemma 2.2.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} [Nontrivial (ℝ^n)]

/-- The positive real diffusion eigenvalues remain nonzero after complexification. -/
theorem frontComplexifiedDiffusion_injective
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) :
    Function.Injective (frontComplexifiedDiffusion D) := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  let J := diffusionCoordinatesEquiv D hD
  have hcoord (w : ℂ^n) : frontComplexifiedDiffusion D w =
      J (fun i ↦ (diffusionEigenvalues D hD i : ℂ) * J.symm w i) := by
    simpa only [J, ContinuousLinearEquiv.apply_symm_apply] using
      complexifiedDiffusion_coordinates D hD (J.symm w)
  intro x y hxy
  rw [hcoord x, hcoord y] at hxy
  have hcoords := J.injective hxy
  apply J.symm.injective
  funext i
  have hne : (diffusionEigenvalues D hD i : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hμ.trans_le (hμle i))
  exact mul_left_cancel₀ hne (congrFun hcoords i)

/-- The diffusion inverse is bounded in the complex state space. -/
theorem exists_frontComplexifiedDiffusion_lower_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) :
    ∃ K ≥ 0, ∀ x : ℂ^n, ‖x‖ ≤ K * ‖frontComplexifiedDiffusion D x‖ := by
  let e : ℂ^n ≃L[ℂ] ℂ^n := (LinearEquiv.ofInjectiveEndo
    (frontComplexifiedDiffusion D).toLinearMap
    (frontComplexifiedDiffusion_injective D hD hDinj)).toContinuousLinearEquiv
  refine ⟨‖e.symm.toContinuousLinearMap‖, norm_nonneg _, fun x ↦ ?_⟩
  calc
    ‖x‖ = ‖e.symm (e x)‖ := by rw [e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _ = ‖e.symm.toContinuousLinearMap‖ * ‖frontComplexifiedDiffusion D x‖ := rfl

/-- Closedness of every complex-frequency longitudinal differential expression with BUC
zeroth-order coefficient, without invoking the spectral-stability hypothesis. -/
theorem isClosed_frontLongitudinalOperator_graph
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℂ) (A : BUC ℝ (ℂ^n →L[ℂ] ℂ^n)) :
    IsClosed (range ((ComplexBUC2.valueCLM (ℂ^n)).prod
      (longitudinalOperator (frontComplexifiedDiffusion D) c q A))) := by
  obtain ⟨K, hK, hbound⟩ := exists_frontComplexifiedDiffusion_lower_bound D hD hDinj
  exact isClosed_longitudinalOperator_graph (frontComplexifiedDiffusion D) hK hbound c q A

/-- The generator graph is exactly the `BUC²` differential-operator graph: the core closure
from heat regularization introduces no extra domain elements. -/
theorem frontDiffusionOperator_graph
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c q : ℝ) :
    range ((ComplexBUC2.valueCLM (ℂ^n)).prod
      (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0)) =
      {p : BUC ℝ (ℂ^n) × BUC ℝ (ℂ^n) |
        (frontDiffusionC0Semigroup D hD c q).HasGeneratorAt p.1 p.2} := by
  exact (isClosed_frontLongitudinalOperator_graph D hD hDinj c q 0).closure_eq.symm.trans
    (closure_frontDiffusionOperator_graph D hD hDinj c q)

/-- Exact generator/domain identification for the principal semigroup of Lemma 2.2. -/
theorem frontDiffusionC0Semigroup_hasGeneratorAt_iff
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℝ) (x y : BUC ℝ (ℂ^n)) :
    (frontDiffusionC0Semigroup D hD c q).HasGeneratorAt x y ↔
      ∃ v : ComplexBUC2 (ℂ^n), ComplexBUC2.value (ℂ^n) v = x ∧
        longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 v = y := by
  constructor
  · intro hxy
    have hm : (x, y) ∈ range ((ComplexBUC2.valueCLM (ℂ^n)).prod
        (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0)) := by
      rw [frontDiffusionOperator_graph D hD hDinj c q]
      exact hxy
    obtain ⟨v, hv⟩ := hm
    exact ⟨v, congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  · rintro ⟨v, rfl, rfl⟩
    exact frontDiffusionC0Semigroup_hasGeneratorAt D hD hDinj c q v

/-- Bundle the principal operator with its actual, now verified, closed graph domain. -/
def frontDiffusionClosedOperator
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c q : ℝ) :
    ClosedOperator ℂ (BUC ℝ (ℂ^n)) (ComplexBUC2 (ℂ^n)) where
  inclusion := ComplexBUC2.valueCLM (ℂ^n)
  inclusion_injective := ComplexBUC2.valueCLM_injective (ℂ^n)
  operator := longitudinalOperator (frontComplexifiedDiffusion D) c q 0
  isClosed_graph := isClosed_frontLongitudinalOperator_graph D hD hDinj c q 0

/-- The full common-domain pencil is closed for every complex parameter, using just smooth
parabolicity and the front hypotheses. This is the operator to which bounded perturbation applies. -/
def frontPencilClosedOperator (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
    (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ) (q : ℂ) :
    ClosedOperator ℂ (BUC ℝ (ℂ^n)) (ComplexBUC2 (ℂ^n)) where
  inclusion := ComplexBUC2.valueCLM (ℂ^n)
  inclusion_injective := ComplexBUC2.valueCLM_injective (ℂ^n)
  operator := frontLongitudinalPencil f D c φ h₁ h₂ q
  isClosed_graph := isClosed_frontLongitudinalOperator_graph D h₁.positive h₁.kernel c q
    (complexFrontDerivativeCoefficient f D c φ h₁ h₂)

end

end Planarwave
