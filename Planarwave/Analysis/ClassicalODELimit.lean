/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Sequences

@[expose] public section

/-!
# Classical limits of regularized longitudinal ODEs

Once the solution and source converge pointwise and are uniformly bounded,
the integrated ODE determines the first derivative from its value at zero.
A convergent subsequence of these initial derivative values suffices. Bounded
convergence on finite intervals then identifies both classical derivatives.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Planarwave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Bounded pointwise convergence can be integrated over any finite interval. -/
theorem tendsto_intervalIntegral_of_bounded_pointwise
    {u : ℕ → ℝ → F} {v : ℝ → F} {M : ℝ}
    (hc : ∀ j, Continuous (u j)) (hb : ∀ j x, ‖u j x‖ ≤ M)
    (hl : ∀ x, Tendsto (fun j ↦ u j x) atTop (𝓝 (v x))) (a b : ℝ) :
    Tendsto (fun j ↦ ∫ x in a..b, u j x) atTop (𝓝 (∫ x in a..b, v x)) :=
  intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M)
    (Eventually.of_forall fun j ↦ (hc j).aestronglyMeasurable)
    (Eventually.of_forall fun j ↦ ae_of_all _ fun x _ ↦ hb j x)
    intervalIntegrable_const (ae_of_all _ fun x _ ↦ hl x)

/-- Identify a limiting derivative by finite-interval integration and the FTC. -/
theorem hasDerivAt_of_bounded_pointwise_limits
    {u v : ℕ → ℝ → F} {χ χ₁ : ℝ → F} {M : ℝ}
    (hv : ∀ j, Continuous (v j)) (hχ₁ : Continuous χ₁)
    (hd : ∀ j x, HasDerivAt (u j) (v j x) x)
    (hb : ∀ j x, ‖v j x‖ ≤ M)
    (hu : ∀ x, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)))
    (hvl : ∀ x, Tendsto (fun j ↦ v j x) atTop (𝓝 (χ₁ x))) (x : ℝ) :
    HasDerivAt χ (χ₁ x) x := by
  have hFTC (y : ℝ) : (∫ t in 0..y, χ₁ t) = χ y - χ 0 := by
    apply tendsto_nhds_unique (tendsto_intervalIntegral_of_bounded_pointwise hv hb hvl 0 y)
    convert (hu y).sub (hu 0) using 1
    ext j
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd j t)
      ((hv j).intervalIntegrable _ _)
  have hdI := (hχ₁.integral_hasStrictDerivAt 0 x).hasDerivAt.add_const (χ 0)
  convert hdI using 1
  ext y
  rw [hFTC, sub_add_cancel]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Fatou transfers an index-independent L1 norm bound to a continuous pointwise limit. -/
theorem integrable_of_bounded_integral_norm_of_pointwise
    {u : ℕ → ℝ → F} {v : ℝ → F} {M : ℝ}
    (hi : ∀ j, Integrable (u j)) (hv : Continuous v)
    (hb : ∀ j, (∫ x, ‖u j x‖) ≤ M)
    (hl : ∀ x, Tendsto (fun j ↦ u j x) atTop (𝓝 (v x))) : Integrable v := by
  refine ⟨hv.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  have hfatou : (∫⁻ x, ‖v x‖ₑ) ≤ liminf (fun j ↦ ∫⁻ x, ‖u j x‖ₑ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun j ↦ ‖u j x‖ₑ) atTop :=
        lintegral_congr_ae (ae_of_all _ fun x ↦ (hl x).enorm.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' fun j ↦ (hi j).aestronglyMeasurable.enorm
  have hbound : liminf (fun j ↦ ∫⁻ x, ‖u j x‖ₑ) atTop ≤ ENNReal.ofReal M := by
    apply liminf_le_of_frequently_le'
    apply Frequently.of_forall
    intro j
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi j)]
    exact ENNReal.ofReal_le_ofReal (hb j)
  exact (hfatou.trans hbound).trans_lt ENNReal.ofReal_lt_top

/-- Passing to a classical two-jet in an invertible-diffusion ODE. Compactness
is used only for the first derivative at zero; the integrated equation gives
convergence everywhere else. -/
theorem exists_classical_adjointODE_limit [ProperSpace F]
    (D : F ≃L[ℝ] F) (c : ℝ) {u v w q : ℕ → ℝ → F} {χ R : ℝ → F}
    (hv : ∀ j, Continuous (v j)) (hw : ∀ j, Continuous (w j))
    (hq : ∀ j, Continuous (q j)) (hχ : Continuous χ) (hR : Continuous R)
    (huv : ∀ j x, HasDerivAt (u j) (v j x) x)
    (hvw : ∀ j x, HasDerivAt (v j) (w j x) x)
    (heq : ∀ j x, D (w j x) - c • v j x + q j x = 0)
    {M Q : ℝ} (hvb : ∀ j x, ‖v j x‖ ≤ M) (hqb : ∀ j x, ‖q j x‖ ≤ Q)
    (hul : ∀ x, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)))
    (hql : ∀ x, Tendsto (fun j ↦ q j x) atTop (𝓝 (R x))) :
    ∃ χ₁ χ₂ : ℝ → F, Continuous χ₁ ∧ Continuous χ₂ ∧
      (∀ x, HasDerivAt χ (χ₁ x) x) ∧ (∀ x, HasDerivAt χ₁ (χ₂ x) x) ∧
      (∀ x, D (χ₂ x) - c • χ₁ x + R x = 0) ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧
        (∀ x, Tendsto (fun j ↦ v (k j) x) atTop (𝓝 (χ₁ x))) ∧
        (∀ x, Tendsto (fun j ↦ w (k j) x) atTop (𝓝 (χ₂ x))) := by
  obtain ⟨a, _, k, hk, hka⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : F)) (r := M))
    (fun j ↦ show v j 0 ∈ Metric.closedBall (0 : F) M by simpa using hvb j 0)
  have hprimitive (j : ℕ) (x : ℝ) :
      v j x = v j 0 + D.symm (c • (u j x - u j 0) - ∫ t in 0..x, q j t) := by
    have hd (t : ℝ) : HasDerivAt (fun z ↦ D (v j z) - c • u j z) (-q j t) t := by
      have hd0 : HasDerivAt (fun z ↦ D (v j z) - c • u j z) (D (w j t) - c • v j t) t := by
        simpa only [Function.comp_def, Pi.sub_apply, Pi.smul_apply] using!
          (D.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hvw j t)).sub
            ((huv j t).const_smul c)
      rwa [eq_neg_of_add_eq_zero_left (heq j t)] at hd0
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      ((hq j).neg.intervalIntegrable 0 x)
    apply D.injective
    rw [map_add, D.apply_symm_apply]
    calc
      D (v j x) = (D (v j x) - c • u j x - (D (v j 0) - c • u j 0)) +
          D (v j 0) + c • (u j x - u j 0) := by rw [smul_sub]; abel
      _ = (-∫ t in 0..x, q j t) + D (v j 0) + c • (u j x - u j 0) := by
        rw [← hFTC, intervalIntegral.integral_neg]
      _ = _ := by abel
  let χ₁ := fun x ↦ a + D.symm (c • (χ x - χ 0) - ∫ t in 0..x, R t)
  have hχ₁ : Continuous χ₁ := continuous_const.add (D.symm.continuous.comp
    ((hχ.sub continuous_const).const_smul c |>.sub
      (intervalIntegral.differentiable_integral_of_continuous hR).continuous))
  have hlv (x : ℝ) : Tendsto (fun j ↦ v (k j) x) atTop (𝓝 (χ₁ x)) := by
    rw [show (fun j ↦ v (k j) x) = (fun j ↦ v (k j) 0 +
      D.symm (c • (u (k j) x - u (k j) 0) - ∫ t in 0..x, q (k j) t)) from
      funext fun j ↦ hprimitive (k j) x]
    exact hka.add (D.symm.continuous.tendsto _ |>.comp
      (((hul x).sub (hul 0)).const_smul c |>.sub
        (tendsto_intervalIntegral_of_bounded_pointwise hq hqb hql 0 x) |>.comp hk.tendsto_atTop))
  have hwexpr (j : ℕ) (x : ℝ) : w j x = D.symm (c • v j x - q j x) := by
    apply D.injective
    rw [D.apply_symm_apply]
    simpa [sub_eq_add_neg, add_comm] using sub_eq_iff_eq_add.mp (eq_sub_of_add_eq (heq j x))
  let χ₂ := fun x ↦ D.symm (c • χ₁ x - R x)
  have hχ₂ : Continuous χ₂ := D.symm.continuous.comp ((hχ₁.const_smul c).sub hR)
  have hlw (x : ℝ) : Tendsto (fun j ↦ w (k j) x) atTop (𝓝 (χ₂ x)) := by
    simp_rw [hwexpr]
    exact D.symm.continuous.tendsto _ |>.comp ((hlv x).const_smul c |>.sub ((hql x).comp hk.tendsto_atTop))
  have hwb (j : ℕ) (x : ℝ) : ‖w j x‖ ≤ ‖D.symm.toContinuousLinearMap‖ * (‖c‖ * M + Q) := by
    rw [hwexpr]
    calc
      _ ≤ ‖D.symm.toContinuousLinearMap‖ * ‖c • v j x - q j x‖ := D.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖D.symm.toContinuousLinearMap‖ * (‖c‖ * ‖v j x‖ + ‖q j x‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [norm_smul] using norm_sub_le (c • v j x) (q j x)) (norm_nonneg _)
      _ ≤ _ := by gcongr <;> [exact hvb j x; exact hqb j x]
  refine ⟨χ₁, χ₂, hχ₁, hχ₂,
    (fun x ↦ hasDerivAt_of_bounded_pointwise_limits (fun j ↦ hv (k j)) hχ₁
      (fun j ↦ huv (k j)) (fun j ↦ hvb (k j))
      (fun x ↦ (hul x).comp hk.tendsto_atTop) hlv x),
    (fun x ↦ hasDerivAt_of_bounded_pointwise_limits (fun j ↦ hw (k j)) hχ₂
      (fun j ↦ hvw (k j)) (fun j ↦ hwb (k j)) hlv hlw x), ?_, k, hk, hlv, hlw⟩
  intro x
  dsimp only [χ₂]
  rw [D.apply_symm_apply]
  abel

end Planarwave
