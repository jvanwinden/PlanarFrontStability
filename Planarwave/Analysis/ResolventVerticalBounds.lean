/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SectorialResolvent

@[expose] public section

/-!
# Vertical-line bounds for sectorial resolvents

The spectral-to-growth step in Section 2 requires control on entire vertical
lines, not only compact subsets of the resolvent. A sectorial estimate controls
the tails; continuity on a compact rectangle controls the middle. The resulting
inverse-linear bound makes the squared resolvent integrable, as required by
the differentiated Laplace inversion formula.
-/

open Filter MeasureTheory Set Topology

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

/-- On a spectral-gap strip, the ambient resolvent decays like the inverse
imaginary part, uniformly in the real part. -/
theorem exists_ambientResolvent_vertical_bound (A : ClosedOperator ℂ E Dom)
    {a C₀ Ω β γ : ℝ} (ha : 0 < a)
    (hsector : ∀ z : ℂ, Ω < z.re + a * |z.im| →
      ‖A.ambientResolvent z‖ ≤ C₀ / (z.re + a * |z.im| - Ω))
    (hres : ∀ z : ℂ, β ≤ z.re → z.re ≤ γ → A.IsInResolvent z) :
    ∃ C > 0, ∀ z : ℂ, β ≤ z.re → z.re ≤ γ →
      ‖A.ambientResolvent z‖ ≤ C / (1 + |z.im|) := by
  let R := (2 * (|Ω| + |β|) + a) / a + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have haR : a * R = 2 * (|Ω| + |β|) + 2 * a := by
    dsimp [R]
    field_simp
    ring
  let K : Set ℂ := Metric.closedBall 0 (|β| + |γ| + R) ∩ {z | β ≤ z.re ∧ z.re ≤ γ}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))
  have hcont : ContinuousOn (fun z : ℂ ↦ (1 + |z.im|) * ‖A.ambientResolvent z‖) K := by
    apply (continuous_const.add Complex.continuous_im.abs).continuousOn.mul
    apply ContinuousOn.norm
    intro z hz
    exact (A.contDiffAt_ambientResolvent (hres z hz.2.1 hz.2.2)).continuousAt.continuousWithinAt
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max (max N (2 * C₀ / a)) 0 + 1, by positivity, ?_⟩
  · intro z hβ hγ
    have hpos : 0 < 1 + |z.im| := by positivity
    apply (le_div_iff₀ hpos).mpr
    have hweight : (1 + |z.im|) * ‖A.ambientResolvent z‖ ≤ max N (2 * C₀ / a) := by
      by_cases hzR : |z.im| ≤ R
      · have hre : |z.re| ≤ |β| + |γ| := by
          rw [abs_le]
          constructor <;> linarith [neg_abs_le β, le_abs_self γ, abs_nonneg β, abs_nonneg γ]
        have hzK : z ∈ K := ⟨by
          simpa only [Metric.mem_closedBall, dist_zero_right] using
            (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hre hzR), hβ, hγ⟩
        have hbound := hN z hzK
        rw [Real.norm_of_nonneg (by positivity)] at hbound
        exact hbound.trans (le_max_left _ _)
      · have hlarge : R < |z.im| := lt_of_not_ge hzR
        have hden : a / 2 * (1 + |z.im|) ≤ z.re + a * |z.im| - Ω := by
          have := mul_lt_mul_of_pos_left hlarge ha
          rw [haR] at this
          nlinarith [le_abs_self Ω, neg_abs_le β]
        have hzsector : Ω < z.re + a * |z.im| := by
          have : 0 < a / 2 * (1 + |z.im|) := by positivity
          linarith
        have hb := (le_div_iff₀ (sub_pos.mpr hzsector)).mp (hsector z hzsector)
        have hh := mul_le_mul_of_nonneg_left hden (norm_nonneg (A.ambientResolvent z))
        have htail : (1 + |z.im|) * ‖A.ambientResolvent z‖ ≤ 2 * C₀ / a := by
          apply (le_div_iff₀ ha).mpr
          nlinarith
        exact htail.trans (le_max_right _ _)
    nlinarith [le_max_left (max N (2 * C₀ / a)) 0]

/-- A resolvent square has an integrable inverse-quadratic vertical majorant. -/
theorem norm_ambientResolvent_sq_le (A : ClosedOperator ℂ E Dom)
    {C β : ℝ}
    (hbound : ∀ y : ℝ, ‖A.ambientResolvent (β + y * Complex.I)‖ ≤ C / (1 + |y|))
    (y : ℝ) :
    ‖(A.ambientResolvent (β + y * Complex.I)).comp
      (A.ambientResolvent (β + y * Complex.I))‖ ≤ C ^ 2 * (1 + y ^ 2)⁻¹ := by
  let R := A.ambientResolvent (β + y * Complex.I)
  calc
    ‖R.comp R‖ ≤ ‖R‖ ^ 2 := by simpa only [pow_two] using R.opNorm_comp_le R
    _ ≤ (C / (1 + |y|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound y) 2
    _ = C ^ 2 / (1 + |y|) ^ 2 := div_pow _ _ _
    _ ≤ C ^ 2 / (1 + y ^ 2) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      nlinarith [abs_nonneg y, sq_abs y]
    _ = C ^ 2 * (1 + y ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- Absolute convergence of the vertical squared-resolvent integral. -/
theorem integrable_ambientResolvent_sq (A : ClosedOperator ℂ E Dom)
    {C β : ℝ}
    (hres : ∀ y : ℝ, A.IsInResolvent (β + y * Complex.I))
    (hbound : ∀ y : ℝ, ‖A.ambientResolvent (β + y * Complex.I)‖ ≤ C / (1 + |y|)) :
    Integrable (fun y : ℝ ↦ (A.ambientResolvent (β + y * Complex.I)).comp
      (A.ambientResolvent (β + y * Complex.I))) := by
  have hc : Continuous (fun y : ℝ ↦ A.ambientResolvent (β + y * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (A.contDiffAt_ambientResolvent (hres y)).continuousAt.comp
      (f := fun y : ℝ ↦ (β : ℂ) + y * Complex.I) (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono' (hc.clm_comp hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall (A.norm_ambientResolvent_sq_le hbound)

end

end Planarwave.ClosedOperator
