/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Definitions
import all Planarwave.Analysis.PhaseFunctional
import all Planarwave.Analysis.ChallengeBridge
import all Planarwave.Analysis.ComplexBUC2

/-!
# The neutral profile projection

This file formalizes the rank-one projection used in the paper,

`P₀ v = ℓ(v) • Φ`,

where `Φ` is a bundled BUC representative of the embedded translation mode and `ℓ` is the phase
functional.  Challenge's normalization gives `ℓ(Φ) = 1`.
-/

open scoped InnerProductSpace
open MeasureTheory

noncomputable section

namespace Planarwave

variable {n : ℕ}

/-- The paper's rank-one neutral profile operator. -/
noncomputable def profileProjection
    (ψ : ℝ → EuclideanSpace ℝ (Fin n)) (hψ : Integrable ψ)
    (Φ : LongitudinalBUC n) : LongitudinalBUC n →L[ℂ] LongitudinalBUC n :=
  (phaseFunctional ψ hψ).smulRight Φ

@[simp]
theorem profileProjection_apply
    (ψ : ℝ → EuclideanSpace ℝ (Fin n)) (hψ : Integrable ψ)
    (Φ v : LongitudinalBUC n) :
    profileProjection ψ hψ Φ v = phaseFunctional ψ hψ v • Φ :=
  rfl

section Normalized

variable {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
variable {D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
variable {c : ℝ} {φ ψ : ℝ → EuclideanSpace ℝ (Fin n)}
variable (hstable : IsSpectrallyStableWithAdjoint f D c φ ψ)
variable (Φ : LongitudinalBUC n)
variable (hΦ : ∀ z, Φ z = embed (deriv φ z))

include hstable hΦ

/-- Challenge's normalization is exactly `ℓ(Φ) = 1`. -/
theorem phaseFunctional_translationMode_eq_one :
    phaseFunctional ψ hstable.integrable Φ = 1 :=
  phaseFunctional_embedded_deriv_eq_one_of_spectralStability hstable Φ hΦ

/-- The neutral profile operator fixes the translation mode. -/
@[simp]
theorem profileProjection_translationMode :
    profileProjection ψ hstable.integrable Φ Φ = Φ := by
  rw [profileProjection_apply, phaseFunctional_translationMode_eq_one hstable Φ hΦ, one_smul]

/-- `P₀` is idempotent. -/
theorem profileProjection_idempotent (v : LongitudinalBUC n) :
    profileProjection ψ hstable.integrable Φ
        (profileProjection ψ hstable.integrable Φ v) =
      profileProjection ψ hstable.integrable Φ v := by
  simp only [profileProjection_apply, map_smul]
  rw [phaseFunctional_translationMode_eq_one hstable Φ hΦ]
  simp

/-- The phase functional is nonzero because it takes value one on `Φ`. -/
theorem phaseFunctional_ne_zero : phaseFunctional ψ hstable.integrable ≠ 0 := by
  intro hzero
  have hone := phaseFunctional_translationMode_eq_one hstable Φ hΦ
  rw [hzero] at hone
  simp at hone

/-- The translation mode itself is nonzero. -/
theorem translationMode_ne_zero : Φ ≠ 0 := by
  intro hzero
  subst Φ
  simpa using phaseFunctional_translationMode_eq_one hstable (0 : LongitudinalBUC n) hΦ

/-- The range of `P₀` is precisely the complex span of the translation mode. -/
theorem range_profileProjection :
    LinearMap.range (profileProjection ψ hstable.integrable Φ).toLinearMap =
      Submodule.span ℂ {Φ} := by
  simpa [profileProjection] using
    ContinuousLinearMap.range_smulRight_apply
      (phaseFunctional_ne_zero hstable Φ hΦ) Φ

/-- The kernel of `P₀` is precisely the kernel of the phase functional. -/
theorem ker_profileProjection :
    LinearMap.ker (profileProjection ψ hstable.integrable Φ).toLinearMap =
      LinearMap.ker (phaseFunctional ψ hstable.integrable).toLinearMap := by
  ext v
  simp only [LinearMap.mem_ker]
  change phaseFunctional ψ hstable.integrable v • Φ = 0 ↔
    phaseFunctional ψ hstable.integrable v = 0
  constructor
  · intro hv
    exact (smul_eq_zero.mp hv).resolve_right (translationMode_ne_zero hstable Φ hΦ)
  · intro hv
    rw [hv]
    apply BUC.ext
    intro z
    change (0 : ℂ) • Φ z = 0
    exact zero_smul ℂ (Φ z)

/-- Challenge's horizontal-kernel hypothesis, rewritten using the supplied bundled translation
mode. -/
theorem horizontal_kernel_iff_pointwise_multiple_translationMode
    (v : ℝ → EuclideanSpace ℂ (Fin n)) :
    IsTransverseResolventSolution f D c φ 0 0 v 0 ↔
      ∃ a : ℂ, ∀ z, v z = a • Φ z := by
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := (hstable.horizontal_kernel v).mp hv
    exact ⟨a, fun z ↦ by rw [ha z, hΦ z]⟩
  · rintro ⟨a, ha⟩
    apply (hstable.horizontal_kernel v).mpr
    exact ⟨a, fun z ↦ by rw [ha z, hΦ z]⟩

/-- On bundled BUC profiles, the homogeneous resolvent kernel is the span of `Φ`. -/
theorem horizontal_kernel_iff_mem_span (v : LongitudinalBUC n) :
    IsTransverseResolventSolution f D c φ 0 0 (v : ℝ → EuclideanSpace ℂ (Fin n)) 0 ↔
      v ∈ Submodule.span ℂ {Φ} := by
  rw [horizontal_kernel_iff_pointwise_multiple_translationMode hstable Φ hΦ]
  constructor
  · rintro ⟨a, ha⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    apply BUC.ext
    intro z
    exact (ha z).symm
  · intro hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨a, fun z ↦ ?_⟩
    exact congrArg (fun q : LongitudinalBUC n ↦ q z) ha |>.symm

/-- Thus the homogeneous resolvent kernel is exactly the range of `P₀`. -/
theorem horizontal_kernel_iff_mem_range_profileProjection (v : LongitudinalBUC n) :
    IsTransverseResolventSolution f D c φ 0 0 (v : ℝ → EuclideanSpace ℂ (Fin n)) 0 ↔
      v ∈ LinearMap.range (profileProjection ψ hstable.integrable Φ).toLinearMap := by
  rw [horizontal_kernel_iff_mem_span hstable Φ hΦ v, range_profileProjection hstable Φ hΦ]

omit hΦ
/-- Challenge's horizontal-solvability hypothesis is precisely vanishing of the bundled phase
functional on `BUC`. -/
theorem phaseFunctional_eq_zero_iff_horizontal_solvable (w : LongitudinalBUC n) :
    phaseFunctional ψ hstable.integrable w = 0 ↔
      ∃ v, IsTransverseResolventSolution f D c φ 0 0 v
        (w : ℝ → EuclideanSpace ℂ (Fin n)) := by
  rw [phaseFunctional_apply]
  have hw : IsBUC (w : ℝ → EuclideanSpace ℂ (Fin n)) := isBUC_coe w
  exact hstable.horizontal_solvability (w : ℝ → EuclideanSpace ℂ (Fin n)) hw
include hΦ

omit hΦ
include hΦ

/-- The complementary summand has zero phase. -/
theorem phaseFunctional_complement_eq_zero (v : LongitudinalBUC n) :
    phaseFunctional ψ hstable.integrable
      (v - profileProjection ψ hstable.integrable Φ v) = 0 := by
  rw [map_sub, profileProjection_apply, map_smul,
    phaseFunctional_translationMode_eq_one hstable Φ hΦ, smul_eq_mul, mul_one, sub_self]

end Normalized

end Planarwave
