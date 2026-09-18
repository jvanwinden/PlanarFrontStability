/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatEquationReal
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-!
# Joint space-time regularity of one-dimensional heat flow
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Gaussian averaging depends differentiably on scale and position when the datum has a BUC
derivative. The dominating function is independent of both parameters. -/
theorem differentiable_gaussianSmooth_uncurry_of_hasDerivAt (f g : BUC ℝ F)
    (hg : ∀ x, HasDerivAt f (g x) x) :
    Differentiable ℝ (fun p : ℝ × ℝ => gaussianSmooth p.1 f p.2) := by
  intro p
  let L : ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun z =>
    ContinuousLinearMap.snd ℝ ℝ ℝ + z • ContinuousLinearMap.fst ℝ ℝ ℝ
  let K : (ℝ × ℝ) → ℝ → (ℝ × ℝ →L[ℝ] F) :=
    fun q z => (L z).smulRight (g (q.2 + q.1 * z))
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hLbound (z : ℝ) : ‖L z‖ ≤ 1 + |z| := by
    calc
      ‖L z‖ ≤ ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ +
          ‖z • ContinuousLinearMap.fst ℝ ℝ ℝ‖ := norm_add_le _ _
      _ = 1 + |z| := by simp [norm_smul, Real.norm_eq_abs]
  have hKcont (q : ℝ × ℝ) : Continuous (K q) := by
    exact ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F).continuous.comp hL).clm_apply
      (g.continuous.comp (by fun_prop))
  have hbound (q : ℝ × ℝ) (z : ℝ) : ‖K q z‖ ≤ (1 + |z|) * ‖g‖ := by
    dsimp only [K]
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (hLbound z) (g.norm_apply_le _) (norm_nonneg _) (by positivity)
  have hdiff (q : ℝ × ℝ) (z : ℝ) :
      HasFDerivAt (fun r : ℝ × ℝ => f (r.2 + r.1 * z)) (K q z) q := by
    have hscalar : HasFDerivAt (fun r : ℝ × ℝ => r.2 + r.1 * z) (L z) q := by
      have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := q)).add
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).const_smul z)
      have heq : (Prod.snd + z • Prod.fst : ℝ × ℝ → ℝ) =
          fun r => r.2 + r.1 * z := by
        funext r
        simp [mul_comm]
      rw [heq] at h
      exact h
    have h := (hg (q.2 + q.1 * z)).hasFDerivAt.comp q hscalar
    have heq : (ContinuousLinearMap.toSpanSingleton ℝ (g (q.2 + q.1 * z))).comp (L z) =
        K q z := by
      apply ContinuousLinearMap.ext
      intro r
      rfl
    rw [heq] at h
    simpa only [Function.comp_def] using h
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q z => f (q.2 + q.1 * z)) (F' := K)
    (bound := fun z : ℝ => (1 + |z|) * ‖g‖) (s := univ) (μ := stdGaussian ℝ)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun q => (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    ((integrable_const ‖f‖).mono'
      (f.continuous.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun z => f.norm_apply_le _))
    (hKcont p).aestronglyMeasurable
    (ae_of_all _ fun z q _ => hbound q z)
    (((integrable_const 1).add integrable_abs_stdGaussian).mul_const ‖g‖)
    (ae_of_all _ fun z q _ => hdiff q z)).differentiableAt

/-- Joint differentiability of the heat flow at positive time, without differentiability
assumptions on the initial datum. -/
theorem differentiableAt_heatFlow_uncurry_real {a : ℝ} (ha : 0 < a)
    (f : BUC ℝ F) (p : ℝ × ℝ) (hp : 0 < p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => heatFlow a q.1 f q.2) p := by
  have hhalf : 0 < p.1 / 2 := by positivity
  let v := heatFlowBUC a (p.1 / 2) f
  let g := heatDerivBUC ha hhalf f
  have hg : ∀ y, HasDerivAt v (g y) y :=
    fun y => ((contDiff_two_heatFlow_real ha hhalf f).differentiable (by norm_num) y).hasDerivAt
  have hs : DifferentiableAt ℝ (fun q : ℝ × ℝ => heatScale a (q.1 - p.1 / 2)) p :=
    (hasDerivAt_heatScale ha (show 0 < p.1 - p.1 / 2 by linarith)).differentiableAt.comp p
      (f := fun q : ℝ × ℝ => q.1 - p.1 / 2) (g := heatScale a)
      (differentiableAt_fst.sub_const (p.1 / 2))
  have h := (differentiable_gaussianSmooth_uncurry_of_hasDerivAt v g hg _).comp p
    (hs.prodMk differentiableAt_snd)
  apply h.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto p).eventually
    (Ioi_mem_nhds (show p.1 / 2 < p.1 by linarith))] with q hq
  change heatFlow a q.1 f q.2 = gaussianSmooth (heatScale a (q.1 - p.1 / 2)) v q.2
  rw [← heatFlow_real_eq_gaussianSmooth]
  have hcoe : (v : ℝ → F) = heatFlow a (p.1 / 2) f := funext (heatFlowBUC_apply _ _ f)
  rw [hcoe, heatFlow_add_time ha.le (sub_pos.mpr hq).le hhalf.le
    f.uniformContinuous f.norm_apply_le, sub_add_cancel]

/-- The joint derivative consists of the time heat operator and the spatial derivative. -/
theorem hasFDerivAt_heatFlow_uncurry_real {a : ℝ} (ha : 0 < a)
    (f : BUC ℝ F) (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasFDerivAt (fun q : ℝ × ℝ => heatFlow a q.1 f q.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (a • deriv (deriv (heatFlow a p.1 f)) p.2) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (deriv (heatFlow a p.1 f) p.2)) p := by
  have h := (differentiableAt_heatFlow_uncurry_real ha f p hp).hasFDerivAt
  have ht := h.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hx := h.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have htval : fderiv ℝ (fun q : ℝ × ℝ => heatFlow a q.1 f q.2) p (1, 0) =
      a • deriv (deriv (heatFlow a p.1 f)) p.2 :=
    ht.unique (hasDerivAt_heatFlow_time_real ha hp f p.2)
  have hxval : fderiv ℝ (fun q : ℝ × ℝ => heatFlow a q.1 f q.2) p (0, 1) =
      deriv (heatFlow a p.1 f) p.2 :=
    hx.unique ((contDiff_two_heatFlow_real ha hp f).differentiable (by norm_num) p.2).hasDerivAt
  have heq : fderiv ℝ (fun q : ℝ × ℝ => heatFlow a q.1 f q.2) p =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (a • deriv (deriv (heatFlow a p.1 f)) p.2) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (deriv (heatFlow a p.1 f) p.2) := by
    apply ContinuousLinearMap.ext
    intro q
    have hq : q = q.1 • (1, 0) + q.2 • (0, 1) := by ext <;> simp
    conv_lhs => rw [hq]
    rw [map_add, map_smul, map_smul, htval, hxval]
    rfl
  rw [heq] at h
  exact h

/-- A positive-time heat orbit has two successive derivatives that are themselves BUC. -/
theorem exists_buc_derivatives_heatFlow_real {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) : ∃ g h : BUC ℝ F,
    (∀ x, HasDerivAt (heatFlow a t f) (g x) x) ∧
    (∀ x, HasDerivAt g (h x) x) := by
  have hhalf : 0 < t / 2 := by positivity
  let v := heatFlowBUC a (t / 2) f
  let g₀ := heatDerivBUC ha hhalf f
  have hg₀ : ∀ y, HasDerivAt v (g₀ y) y :=
    fun y => ((contDiff_two_heatFlow_real ha hhalf f).differentiable (by norm_num) y).hasDerivAt
  have hsplit : heatFlow a t f = heatFlow a (t / 2) v := by
    have hcoe : (v : ℝ → F) = heatFlow a (t / 2) f := funext (heatFlowBUC_apply _ _ f)
    rw [hcoe, heatFlow_add_time ha.le hhalf.le hhalf.le f.uniformContinuous f.norm_apply_le,
      add_halves]
  refine ⟨heatFlowBUC a (t / 2) g₀, heatDerivBUC ha hhalf g₀, ?_, ?_⟩
  · intro x
    rw [hsplit]
    exact hasDerivAt_heatFlow_of_hasDerivAt a (t / 2) v g₀ hg₀ x
  · intro x
    exact ((contDiff_two_heatFlow_real ha hhalf g₀).differentiable (by norm_num) x).hasDerivAt

/-- Joint space-time smoothness to every finite order at positive times. -/
theorem contDiffOn_nat_heatFlow_uncurry_real (k : ℕ) {a : ℝ} (ha : 0 < a)
    (f : BUC ℝ F) :
    ContDiffOn ℝ k (fun p : ℝ × ℝ => heatFlow a p.1 f p.2) (Ioi 0 ×ˢ univ) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  induction k generalizing f with
  | zero =>
    apply contDiffOn_zero.mpr
    intro p hp
    exact (differentiableAt_heatFlow_uncurry_real ha f p hp.1).continuousAt.continuousWithinAt
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hopen]
    refine ⟨fun p hp => (differentiableAt_heatFlow_uncurry_real ha f p hp.1).differentiableWithinAt,
      by simp, ?_⟩
    intro p hp
    have hppos : 0 < p.1 := hp.1
    have hr : 0 < p.1 / 2 := by positivity
    let v := heatFlowBUC a (p.1 / 2) f
    obtain ⟨g, h, hg, hh⟩ := exists_buc_derivatives_heatFlow_real ha hr f
    have hg' : ∀ x, HasDerivAt v (g x) x := hg
    let shift : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 - p.1 / 2, q.2)
    have hshift : ContDiff ℝ k shift := by dsimp [shift]; fun_prop
    have hmem : shift p ∈ Ioi 0 ×ˢ (univ : Set ℝ) :=
      ⟨by change 0 < p.1 - p.1 / 2; linarith, mem_univ _⟩
    have hcg : ContDiffAt ℝ k (fun q : ℝ × ℝ => heatFlow a (q.1 - p.1 / 2) g q.2) p :=
      ((ih g).contDiffAt (hopen.mem_nhds hmem)).comp p hshift.contDiffAt
    have hch : ContDiffAt ℝ k (fun q : ℝ × ℝ => heatFlow a (q.1 - p.1 / 2) h q.2) p :=
      ((ih h).contDiffAt (hopen.mem_nhds hmem)).comp p hshift.contDiffAt
    let J : ℝ × ℝ → (ℝ × ℝ →L[ℝ] F) := fun q =>
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (a • heatFlow a (q.1 - p.1 / 2) h q.2) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (heatFlow a (q.1 - p.1 / 2) g q.2)
    have hJ : ContDiffAt ℝ k J p := by
      exact (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F)
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).contDiff.contDiffAt.comp p (hch.const_smul a)).add
        ((((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F)
          (ContinuousLinearMap.snd ℝ ℝ ℝ)).contDiff.contDiffAt).comp p hcg)
    apply (hJ.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [(continuous_fst.tendsto p).eventually
      (Ioi_mem_nhds (show p.1 / 2 < p.1 by linarith))] with q hq
    have hqpos : 0 < q.1 := hr.trans hq
    rw [(hasFDerivAt_heatFlow_uncurry_real ha f q hqpos).fderiv]
    have hsplit : heatFlow a q.1 f = heatFlow a (q.1 - p.1 / 2) v := by
      have hcoe : (v : ℝ → F) = heatFlow a (p.1 / 2) f := funext (heatFlowBUC_apply _ _ f)
      rw [hcoe, heatFlow_add_time ha.le (sub_pos.mpr hq).le hr.le
        f.uniformContinuous f.norm_apply_le, sub_add_cancel]
    rw [hsplit, deriv_heatFlow_of_hasDerivAt a _ v g hg', deriv_heatFlow_of_hasDerivAt a _ g h hh]

/-- The heat orbit is jointly smooth in time and space on the positive-time half-plane. -/
theorem contDiffOn_infty_heatFlow_uncurry_real {a : ℝ} (ha : 0 < a) (f : BUC ℝ F) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => heatFlow a p.1 f p.2) (Ioi 0 ×ˢ univ) :=
  contDiffOn_infty.mpr fun k => contDiffOn_nat_heatFlow_uncurry_real k ha f

end

end Planarwave
