/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfPhase

@[expose] public section

/-!
# BUC derivatives of the small inverse Cole--Hopf transform

On `|β ξ| ≤ 1/2`, the inverse derivative `(1 + β ξ)⁻¹` is bounded
by two and is Lipschitz as a BUC field. Consequently a continuous BUC
derivative of ξ gives a continuous BUC derivative and gradient of σ.
-/

open Set
open scoped Gradient

namespace Planarwave

noncomputable section

theorem norm_coleHopfInv_slope_le_two {β x : ℝ} (hx : |β * x| ≤ 1 / 2) :
    ‖(1 + β * x)⁻¹‖ ≤ 2 := by
  have hp : 0 < 1 + β * x := by linarith [(abs_le.mp hx).1]
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp, inv_eq_one_div]
  exact (div_le_iff₀ hp).mpr (by linarith [(abs_le.mp hx).1])

/-- The inverse derivative has a uniform Lipschitz constant on the
small range, valid also when `β = 0`. -/
theorem norm_coleHopfInv_slope_sub_le {β x y : ℝ}
    (hx : |β * x| ≤ 1 / 2) (hy : |β * y| ≤ 1 / 2) :
    ‖(1 + β * x)⁻¹ - (1 + β * y)⁻¹‖ ≤ (4 * |β|) * ‖x - y‖ := by
  have hxn : 1 + β * x ≠ 0 := by linarith [(abs_le.mp hx).1]
  have hyn : 1 + β * y ≠ 0 := by linarith [(abs_le.mp hy).1]
  have heq : (1 + β * x)⁻¹ - (1 + β * y)⁻¹ =
      ((1 + β * x)⁻¹ * (1 + β * y)⁻¹) * (β * (y - x)) := by
    field_simp
    ring
  rw [heq, norm_mul, norm_mul, norm_mul, norm_sub_rev y x]
  calc
    _ ≤ (2 * 2) * (‖β‖ * ‖x - y‖) := by
      gcongr
      · exact norm_coleHopfInv_slope_le_two hx
      · exact norm_coleHopfInv_slope_le_two hy
    _ = _ := by rw [Real.norm_eq_abs]; ring

section BUC

variable {E : Type*} [PseudoMetricSpace E]

/-- The actual inverse derivative composed with a small BUC field. -/
def coleHopfInvSlopeSmallBUC (β : ℝ) (ξ : BUC E ℝ) (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) : BUC E ℝ :=
  ξ.compOnIcc (fun x ↦ (1 + β * x)⁻¹)
    ((continuousOn_const.add (continuousOn_id.const_mul β)).inv₀ (fun x hx ↦ by
      have hp := mem_coleHopfDomain.mp (Icc_subset_coleHopfDomain_of_small_radius hsmall hx)
      change 1 + β * x ≠ 0
      linarith))
    (fun x ↦ abs_le.mp (ξ.norm_apply_le x))

@[simp] theorem coleHopfInvSlopeSmallBUC_apply (β : ℝ) (ξ : BUC E ℝ)
    (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) (x : E) :
    coleHopfInvSlopeSmallBUC β ξ hsmall x = (1 + β * ξ x)⁻¹ := rfl

theorem norm_coleHopfInvSlopeSmallBUC_le (β : ℝ) (ξ : BUC E ℝ)
    (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) : ‖coleHopfInvSlopeSmallBUC β ξ hsmall‖ ≤ 2 := by
  apply (BUC.norm_le (by norm_num)).mpr
  intro x
  apply norm_coleHopfInv_slope_le_two
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (ξ.norm_apply_le x) (abs_nonneg β)).trans hsmall

theorem norm_coleHopfInvSlopeSmallBUC_sub_le (β : ℝ) (ξ η : BUC E ℝ)
    (hξ : |β| * ‖ξ‖ ≤ 1 / 2) (hη : |β| * ‖η‖ ≤ 1 / 2) :
    ‖coleHopfInvSlopeSmallBUC β ξ hξ - coleHopfInvSlopeSmallBUC β η hη‖ ≤
      (4 * |β|) * ‖ξ - η‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  have hx : |β * ξ x| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (ξ.norm_apply_le x) (abs_nonneg β)).trans hξ
  have hy : |β * η x| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (η.norm_apply_le x) (abs_nonneg β)).trans hη
  exact (norm_coleHopfInv_slope_sub_le hx hy).trans
    (mul_le_mul_of_nonneg_left ((ξ - η).norm_apply_le x) (by positivity))

/-- The inverse derivative coefficient is continuous in BUC norm along
a small continuous trajectory, including both endpoints. -/
theorem exists_continuous_coleHopfInvSlope_on {β T : ℝ} (ξ : ℝ → BUC E ℝ)
    (hξ : ContinuousOn ξ (Icc 0 T)) (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2) :
    ∃ S : ℝ → BUC E ℝ, ContinuousOn S (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, (∀ x, S t x = (1 + β * ξ t x)⁻¹) ∧ ‖S t‖ ≤ 2 := by
  classical
  let S := fun t ↦ if ht : t ∈ Icc 0 T then coleHopfInvSlopeSmallBUC β (ξ t) (hsmall t ht) else 0
  have heq : ∀ t (ht : t ∈ Icc 0 T), S t = coleHopfInvSlopeSmallBUC β (ξ t) (hsmall t ht) := by
    intro t ht
    simp only [S, dif_pos ht]
  refine ⟨S, ?_, fun t ht ↦ ?_⟩
  · intro t ht
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hden : 0 < 4 * |β| + 1 := by positivity
    obtain ⟨δ, hδ, hc⟩ := Metric.continuousWithinAt_iff.mp (hξ t ht)
      (ε / (4 * |β| + 1)) (div_pos hε hden)
    refine ⟨δ, hδ, fun r hr hrt ↦ ?_⟩
    have hdiff := norm_coleHopfInvSlopeSmallBUC_sub_le β (ξ r) (ξ t) (hsmall r hr) (hsmall t ht)
    rw [← heq r hr, ← heq t ht] at hdiff
    have hnear := hc hr hrt
    rw [dist_eq_norm] at hnear ⊢
    calc
      _ ≤ (4 * |β|) * ‖ξ r - ξ t‖ := hdiff
      _ ≤ (4 * |β| + 1) * ‖ξ r - ξ t‖ := by gcongr; linarith
      _ < (4 * |β| + 1) * (ε / (4 * |β| + 1)) := mul_lt_mul_of_pos_left hnear hden
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hden)
  · rw [heq t ht]
    exact ⟨fun _ ↦ rfl, norm_coleHopfInvSlopeSmallBUC_le β (ξ t) (hsmall t ht)⟩

end BUC

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance inverseColeHopfDerivativeNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance inverseColeHopfDerivativeNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] ℝ)) := inferInstance
local instance inverseColeHopfScalarBUCNormedAddCommGroup :
    NormedAddCommGroup (BUC E ℝ) := inferInstance
local instance inverseColeHopfScalarBUCNormedSpace :
    NormedSpace ℝ (BUC E ℝ) := inferInstance

omit [FiniteDimensional ℝ E] in
/-- The inverse phase has a genuine BUC derivative, continuous in time,
whose norm is at most twice that of the transformed derivative. -/
theorem exists_coleHopfInv_buc_fderivative {β T : ℝ} {ξ σ : ℝ → BUC E ℝ}
    (hξ : ContinuousOn ξ (Icc 0 T)) (q : ℝ → BUC E (E →L[ℝ] ℝ))
    (hq : ContinuousOn q (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x)
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hσ : ∀ t ∈ Icc 0 T, ∀ x, σ t x = coleHopfInv β (ξ t x)) :
    ∃ Q : ℝ → BUC E (E →L[ℝ] ℝ), ContinuousOn Q (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, (∀ x, HasFDerivAt (σ t) (Q t x) x) ∧ ‖Q t‖ ≤ 2 * ‖q t‖ := by
  obtain ⟨S, hSc, hS⟩ := exists_continuous_coleHopfInvSlope_on ξ hξ hsmall
  refine ⟨fun t ↦ BUC.smulBUC (S t) (q t), ?_, ?_⟩
  · let B : BUC E ℝ →L[ℝ] BUC E (E →L[ℝ] ℝ) →L[ℝ] BUC E (E →L[ℝ] ℝ) :=
      BUC.bilinearBUCCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    have hB : ContinuousOn (fun t ↦ B (S t)) (Icc 0 T) := B.continuous.comp_continuousOn hSc
    exact hB.clm_apply hq
  · intro t ht
    refine ⟨?_, (BUC.norm_smulBUC_le (S t) (q t)).trans (by gcongr; exact (hS t ht).2)⟩
    intro x
    have hx : ξ t x ∈ coleHopfDomain β :=
      Icc_subset_coleHopfDomain_of_small_radius (hsmall t ht) (abs_le.mp ((ξ t).norm_apply_le x))
    have heq : (σ t : E → ℝ) = coleHopfInv β ∘ ξ t := funext (hσ t ht)
    rw [heq, BUC.smulBUC_apply, (hS t ht).1 x]
    exact (hasDerivAt_coleHopfInv hx).comp_hasFDerivAt x (hd t ht x)

/-- The phase gradient used in the nonlinear estimates is an actual
BUC vector field, continuous in time, with the same factor-two bound. -/
theorem exists_coleHopfInv_buc_gradient {β T : ℝ} {ξ σ : ℝ → BUC E ℝ}
    (hξ : ContinuousOn ξ (Icc 0 T)) (q : ℝ → BUC E (E →L[ℝ] ℝ))
    (hq : ContinuousOn q (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (ξ t) (q t x) x)
    (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2)
    (hσ : ∀ t ∈ Icc 0 T, ∀ x, σ t x = coleHopfInv β (ξ t x)) :
    ∃ s : ℝ → BUC E E, ContinuousOn s (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, (∀ x, s t x = ∇ (σ t : E → ℝ) x) ∧ ‖s t‖ ≤ 2 * ‖q t‖ := by
  obtain ⟨Q, hQc, hdQ⟩ := exists_coleHopfInv_buc_fderivative hξ q hq hd hsmall hσ
  let L := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
  refine ⟨fun t ↦ BUC.postcompCLM L (Q t), (BUC.postcompCLM L).continuous.comp_continuousOn hQc, ?_⟩
  intro t ht
  refine ⟨?_, ?_⟩
  · intro x
    change (InnerProductSpace.toDual ℝ E).symm (Q t x) =
      (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (σ t) x)
    rw [((hdQ t ht).1 x).fderiv]
  · apply le_trans _ (hdQ t ht).2
    apply (BUC.norm_le (norm_nonneg (Q t))).mpr
    intro x
    change ‖(InnerProductSpace.toDual ℝ E).symm (Q t x)‖ ≤ ‖Q t‖
    simpa only [LinearIsometryEquiv.norm_map] using (Q t).norm_apply_le x

end Derivative

end

end Planarwave
