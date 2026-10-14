/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.NonlinearVolterra
public import Planarwave.Analysis.IntegralGronwall

@[expose] public section

/-!
# Uniqueness of bounded nonlinear mild solutions

The local contraction produces a solution on a small time interval. To
restart and glue these solutions, uniqueness is needed on arbitrary compact
intervals, not just inside the contraction's chosen invariant ball.
Integral Grönwall gives this uniqueness, together with continuous dependence
on initial data, using only a Lipschitz bound on the range of the two paths.
This is one of the standard semilinear continuation ingredients used in the
paper's final proof.
-/

open Set MeasureTheory

namespace Planarwave

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Stability on a bounded range for two nonlinear mild solutions. There
is no smallness restriction on the final time, the operator bound, or the
Lipschitz constant. Strong joint continuity suffices at time zero. -/
theorem norm_sub_le_exp_of_nonlinearVolterra
    (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2))
    (F : X → X) (hF : Continuous F)
    {T M L R : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hAb : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M)
    (hFL : ∀ y z, ‖y‖ ≤ R → ‖z‖ ≤ R → ‖F y - F z‖ ≤ L * ‖y - z‖)
    {x y : X} {u v : ℝ → X}
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hub : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ R) (hvb : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ R)
    (hmu : ∀ t ∈ Icc 0 T, u t = A t x + ∫ r in 0..t, A (t - r) (F (u r)))
    (hmv : ∀ t ∈ Icc 0 T, v t = A t y + ∫ r in 0..t, A (t - r) (F (v r))) :
    ∀ t ∈ Icc 0 T, ‖u t - v t‖ ≤ M * ‖x - y‖ * Real.exp (M * L * t) := by
  have hdiff : ContinuousOn (fun r ↦ ‖u r - v r‖) (Icc 0 T) := (hu.sub hv).norm
  have hi : ∀ t ∈ Icc 0 T, ‖u t - v t‖ ≤
      M * ‖x - y‖ + ∫ r in (0 : ℝ)..t, (M * L) * ‖u r - v r‖ := by
    intro t ht
    have hsub : uIcc (0 : ℝ) t ⊆ Icc 0 T := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hcu : ContinuousOn (fun r ↦ A (t - r) (F (u r))) (Icc 0 T) :=
      hA.comp_continuousOn ((continuousOn_const.sub continuousOn_id).prodMk
        (hF.comp_continuousOn hu))
    have hcv : ContinuousOn (fun r ↦ A (t - r) (F (v r))) (Icc 0 T) :=
      hA.comp_continuousOn ((continuousOn_const.sub continuousOn_id).prodMk
        (hF.comp_continuousOn hv))
    have hiu : IntervalIntegrable (fun r ↦ A (t - r) (F (u r))) volume 0 t :=
      (hcu.mono hsub).intervalIntegrable
    have hiv : IntervalIntegrable (fun r ↦ A (t - r) (F (v r))) volume 0 t :=
      (hcv.mono hsub).intervalIntegrable
    have hdint : IntervalIntegrable
        (fun r ↦ A (t - r) (F (u r)) - A (t - r) (F (v r))) volume 0 t :=
      hiu.sub hiv
    have hbint : IntervalIntegrable (fun r ↦ (M * L) * ‖u r - v r‖) volume 0 t :=
      ((continuousOn_const.mul hdiff).mono hsub).intervalIntegrable
    have hpoint : ∀ r ∈ Icc 0 t,
        ‖A (t - r) (F (u r)) - A (t - r) (F (v r))‖ ≤
          (M * L) * ‖u r - v r‖ := by
      intro r hr
      have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
      rw [← map_sub]
      calc
        _ ≤ M * ‖F (u r) - F (v r)‖ :=
          ((A _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
            (hAb _ ⟨sub_nonneg.mpr hr.2, by linarith [hr.1, ht.2]⟩) (norm_nonneg _))
        _ ≤ M * (L * ‖u r - v r‖) :=
          mul_le_mul_of_nonneg_left (hFL _ _ (hub _ hrT) (hvb _ hrT)) hM
        _ = _ := (mul_assoc _ _ _).symm
    have hint : ‖∫ r in (0 : ℝ)..t,
        A (t - r) (F (u r)) - A (t - r) (F (v r))‖ ≤
          ∫ r in (0 : ℝ)..t, (M * L) * ‖u r - v r‖ :=
      (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
        (intervalIntegral.integral_mono_on ht.1 hdint.norm hbint hpoint)
    rw [hmu t ht, hmv t ht, ← sub_add_sub_comm, ← map_sub,
      ← intervalIntegral.integral_sub hiu hiv]
    exact (norm_add_le _ _).trans (add_le_add
      (((A t).le_opNorm (x - y)).trans
        (mul_le_mul_of_nonneg_right (hAb t ht) (norm_nonneg _))) hint)
  have hgr := le_exp_integral_of_le_add_integral_mul hT hdiff
    (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ M * L) (Icc 0 T))
    (fun _ _ ↦ mul_nonneg hM hL) hi
  intro t ht
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm t (M * L)]
    using hgr t ht

/-- Two bounded mild solutions with the same initial datum agree on their
whole common compact time interval. This is the uniqueness statement needed
to glue local solutions and define a maximal solution. -/
theorem eqOn_of_nonlinearVolterra
    (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2))
    (F : X → X) (hF : Continuous F)
    {T M L R : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hAb : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M)
    (hFL : ∀ y z, ‖y‖ ≤ R → ‖z‖ ≤ R → ‖F y - F z‖ ≤ L * ‖y - z‖)
    {x : X} {u v : ℝ → X}
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hub : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ R) (hvb : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ R)
    (hmu : ∀ t ∈ Icc 0 T, u t = A t x + ∫ r in 0..t, A (t - r) (F (u r)))
    (hmv : ∀ t ∈ Icc 0 T, v t = A t x + ∫ r in 0..t, A (t - r) (F (v r))) :
    EqOn u v (Icc 0 T) := by
  intro t ht
  have h := norm_sub_le_exp_of_nonlinearVolterra A hA F hF hT hM hL hAb hFL
    hu hv hub hvb hmu hmv t ht
  simpa only [sub_self, norm_zero, mul_zero, zero_mul, norm_le_zero_iff, sub_eq_zero]
    using h

/-- With a Lipschitz constant on every bounded ball, the continuity of
the trajectories supplies the common range bound automatically. -/
theorem eqOn_of_nonlinearVolterra_lipschitzOn_balls
    (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2))
    (F : X → X) (hF : Continuous F)
    (hFL : ∀ R : ℝ, ∃ L > 0, ∀ y z, ‖y‖ ≤ R → ‖z‖ ≤ R →
      ‖F y - F z‖ ≤ L * ‖y - z‖)
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hAb : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M)
    {x : X} {u v : ℝ → X}
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hmu : ∀ t ∈ Icc 0 T, u t = A t x + ∫ r in 0..t, A (t - r) (F (u r)))
    (hmv : ∀ t ∈ Icc 0 T, v t = A t x + ∫ r in 0..t, A (t - r) (F (v r))) :
    EqOn u v (Icc 0 T) := by
  obtain ⟨Ru, hRu⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  obtain ⟨Rv, hRv⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  obtain ⟨L, hL, hLip⟩ := hFL (max Ru Rv)
  exact eqOn_of_nonlinearVolterra A hA F hF hT hM hL.le hAb hLip hu hv
    (fun t ht ↦ (hRu t ht).trans (le_max_left _ _))
    (fun t ht ↦ (hRv t ht).trans (le_max_right _ _)) hmu hmv

end

end Planarwave
