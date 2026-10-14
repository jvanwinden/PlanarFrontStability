/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupDuhamel
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section

/-!
# Local nonlinear Volterra equations

The local-existence step in the paper's final proof is a contraction on a
closed ball of continuous Banach-valued paths. Only strong joint continuity
of the linear evolution is used, not operator-norm continuity at time zero.
The lifetime is uniform on bounded sets of initial data. No global
Lipschitz or boundedness assumption on the nonlinearity is imposed.
-/

open Set MeasureTheory

namespace Planarwave

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Nonlinear Duhamel path for a strongly continuous linear evolution. -/
def nonlinearVolterraPath (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2)) (F : X → X) (hF : Continuous F)
    (T : NNReal) (x : X) (u : C0Semigroup.TimePath (E := X) T) :
    C0Semigroup.TimePath (E := X) T where
  toFun t := A t x + ∫ r in 0..(t : ℝ), A (t - r) (F (C0Semigroup.extendTimePath u r))
  continuous_toFun := by
    have hi : Continuous (fun p : ℝ × ℝ ↦
        A (p.1 - p.2) (F (C0Semigroup.extendTimePath u p.2))) :=
      hA.comp ((continuous_fst.sub continuous_snd).prodMk
        ((hF.comp (C0Semigroup.continuous_extendTimePath u)).comp continuous_snd))
    have hint : Continuous (fun t : ℝ ↦
        ∫ r in 0..t, A (t - r) (F (C0Semigroup.extendTimePath u r))) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hi continuous_id
    exact ((hA.comp (continuous_id.prodMk continuous_const)).add hint).comp
      continuous_subtype_val

omit [CompleteSpace X] in
/-- The small time factor in the invariant-ball estimate. -/
theorem norm_nonlinearVolterraPath_le (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2)) (F : X → X) (hF : Continuous F)
    (T : NNReal) {M B C R : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAb : ∀ t ∈ Icc 0 (T : ℝ), ‖A t‖ ≤ M)
    (hFb : ∀ y, ‖y‖ ≤ R → ‖F y‖ ≤ C) {x : X} (hx : ‖x‖ ≤ B)
    {u : C0Semigroup.TimePath (E := X) T} (hu : ‖u‖ ≤ R) :
    ‖nonlinearVolterraPath A hA F hF T x u‖ ≤ M * B + M * C * T := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hi : ‖∫ r in 0..(t : ℝ), A (t - r) (F (C0Semigroup.extendTimePath u r))‖ ≤
      M * C * (t : ℝ) := by
    have hb : ∀ r ∈ uIoc (0 : ℝ) (t : ℝ),
        ‖A (t - r) (F (C0Semigroup.extendTimePath u r))‖ ≤ M * C := by
      intro r hr
      rw [uIoc_of_le t.2.1] at hr
      exact ((A _).le_opNorm _).trans (mul_le_mul
        (hAb _ ⟨by linarith [hr.2], by linarith [hr.1, t.2.2]⟩)
        (hFb _ ((u.norm_coe_le_norm _).trans hu)) (norm_nonneg _) hM)
    simpa only [sub_zero, abs_of_nonneg t.2.1] using!
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  exact (norm_add_le _ _).trans (add_le_add
    (((A _).le_opNorm x).trans (mul_le_mul (hAb _ t.2) hx (norm_nonneg _) hM))
    (hi.trans (mul_le_mul_of_nonneg_left t.2.2 (mul_nonneg hM hC))))

omit [CompleteSpace X] in
/-- The difference estimate for the nonlinear Picard map on a fixed ball. -/
theorem norm_nonlinearVolterraPath_sub_le (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2)) (F : X → X) (hF : Continuous F)
    (T : NNReal) {M L R : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hAb : ∀ t ∈ Icc 0 (T : ℝ), ‖A t‖ ≤ M)
    (hFL : ∀ y z, ‖y‖ ≤ R → ‖z‖ ≤ R → ‖F y - F z‖ ≤ L * ‖y - z‖)
    (x : X) {u v : C0Semigroup.TimePath (E := X) T} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖nonlinearVolterraPath A hA F hF T x u - nonlinearVolterraPath A hA F hF T x v‖ ≤
      (M * L * T) * ‖u - v‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hc (w : C0Semigroup.TimePath (E := X) T) : Continuous
      (fun r : ℝ ↦ A (t - r) (F (C0Semigroup.extendTimePath w r))) :=
    hA.comp ((continuous_const.sub continuous_id).prodMk
      (hF.comp (C0Semigroup.continuous_extendTimePath w)))
  change ‖(A t x + _) - (A t x + _)‖ ≤ _
  rw [add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub ((hc u).intervalIntegrable _ _) ((hc v).intervalIntegrable _ _)]
  have hb : ∀ r ∈ uIoc (0 : ℝ) (t : ℝ),
      ‖A (t - r) (F (C0Semigroup.extendTimePath u r)) -
        A (t - r) (F (C0Semigroup.extendTimePath v r))‖ ≤ M * L * ‖u - v‖ := by
    intro r hr
    rw [uIoc_of_le t.2.1] at hr
    rw [← map_sub]
    calc
      _ ≤ M * ‖F (C0Semigroup.extendTimePath u r) - F (C0Semigroup.extendTimePath v r)‖ :=
        ((A _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
          (hAb _ ⟨by linarith [hr.2], by linarith [hr.1, t.2.2]⟩) (norm_nonneg _))
      _ ≤ M * (L * ‖C0Semigroup.extendTimePath u r - C0Semigroup.extendTimePath v r‖) :=
        mul_le_mul_of_nonneg_left (hFL _ _ ((u.norm_coe_le_norm _).trans hu)
          ((v.norm_coe_le_norm _).trans hv)) hM
      _ ≤ M * (L * ‖u - v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm _) hL) hM
      _ = _ := by ring
  have hi : ‖∫ r in 0..(t : ℝ), A (t - r) (F (C0Semigroup.extendTimePath u r)) -
      A (t - r) (F (C0Semigroup.extendTimePath v r))‖ ≤ (M * L * ‖u - v‖) * (t : ℝ) := by
    simpa only [sub_zero, abs_of_nonneg t.2.1] using!
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  exact hi.trans (by
    calc
      _ ≤ (M * L * ‖u - v‖) * (T : ℝ) :=
        mul_le_mul_of_nonneg_left t.2.2 (by positivity)
      _ = _ := by ring)

/-- Local existence and uniqueness in the invariant ball. -/
theorem existsUnique_nonlinearVolterraPath (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2)) (F : X → X) (hF : Continuous F)
    (T : NNReal) {M B C L R : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hAb : ∀ t ∈ Icc 0 (T : ℝ), ‖A t‖ ≤ M)
    (hFb : ∀ y, ‖y‖ ≤ R → ‖F y‖ ≤ C)
    (hFL : ∀ y z, ‖y‖ ≤ R → ‖z‖ ≤ R → ‖F y - F z‖ ≤ L * ‖y - z‖)
    (hinv : M * B + M * C * T ≤ R) (hsmall : M * L * T < 1)
    {x : X} (hx : ‖x‖ ≤ B) :
    ∃! u : C0Semigroup.TimePath (E := X) T,
      ‖u‖ ≤ R ∧ ∀ t, u t = A t x +
        ∫ r in 0..(t : ℝ), A (t - r) (F (C0Semigroup.extendTimePath u r)) := by
  let S : Set (C0Semigroup.TimePath (E := X) T) := {u | ‖u‖ ≤ R}
  let Φ := nonlinearVolterraPath A hA F hF T x
  have hclosed : IsClosed S := isClosed_le continuous_norm continuous_const
  have hmap : MapsTo Φ S S := fun u hu ↦
    (norm_nonlinearVolterraPath_le A hA F hF T hM hB hC hAb hFb hx hu).trans hinv
  have hcontract : ContractingWith ⟨M * L * T, by positivity⟩ (hmap.restrict Φ S S) := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
    simpa only [Subtype.dist_eq, dist_eq_norm] using!
      norm_nonlinearVolterraPath_sub_le A hA F hF T hM hL hAb hFL x u.2 v.2
  obtain ⟨u, hu, hfix, _⟩ := hcontract.exists_fixedPoint' hclosed.isComplete hmap
    (x := 0) (show (0 : C0Semigroup.TimePath (E := X) T) ∈ S by simpa [S] using hR)
    (edist_ne_top _ _)
  refine ⟨u, ⟨hu, fun t ↦ (congrArg (fun w ↦ w t) hfix).symm⟩, ?_⟩
  intro v hv
  have hvfix : Function.IsFixedPt Φ v := ContinuousMap.ext fun t ↦ (hv.2 t).symm
  have heq := hcontract.fixedPoint_unique'
    (x := ⟨v, hv.1⟩) (y := ⟨u, hu⟩)
    (Subtype.ext hvfix) (Subtype.ext hfix)
  exact congrArg Subtype.val heq

/-- Uniform local lifetime for a nonlinearity bounded and Lipschitz on
each bounded ball. The returned path is continuous on all real times by
constant extension; its mild equation is asserted only on `[0,T]`. -/
theorem exists_local_nonlinearVolterra (A : ℝ → X →L[ℝ] X)
    (hA : Continuous (fun p : ℝ × X ↦ A p.1 p.2))
    (hA₀ : A 0 = ContinuousLinearMap.id ℝ X)
    (F : X → X) (hF : Continuous F)
    (hFb : ∀ R : ℝ, ∃ C > 0, ∀ y, ‖y‖ ≤ R → ‖F y‖ ≤ C)
    (hFL : ∀ R : ℝ, ∃ L > 0, ∀ y z, ‖y‖ ≤ R → ‖z‖ ≤ R →
      ‖F y - F z‖ ≤ L * ‖y - z‖)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hAb : ∀ t ∈ Icc (0 : ℝ) 1, ‖A t‖ ≤ M) :
    ∃ T > 0, T ≤ 1 ∧ ∀ x : X, ‖x‖ ≤ B → ∃ u : ℝ → X,
      Continuous u ∧ u 0 = x ∧ (∀ t, ‖u t‖ ≤ M * B + 1) ∧
        ∀ t ∈ Icc 0 T, u t = A t x + ∫ r in 0..t, A (t - r) (F (u r)) := by
  let R := M * B + 1
  obtain ⟨C, hC, hCb⟩ := hFb R
  obtain ⟨L, hL, hLb⟩ := hFL R
  let q := M * C + M * L + 1
  have hq : 0 < q := by dsimp [q]; positivity
  let τ := min 1 (1 / (2 * q))
  have hτ : 0 < τ := lt_min zero_lt_one (by positivity)
  have hτ₁ : τ ≤ 1 := min_le_left _ _
  have hτq : τ ≤ 1 / (2 * q) := min_le_right _ _
  have hMC : M * C * τ < 1 := by
    calc
      _ ≤ M * C * (1 / (2 * q)) := mul_le_mul_of_nonneg_left hτq (by positivity)
      _ < 1 := by rw [mul_one_div, div_lt_iff₀ (by positivity)]; dsimp [q]; nlinarith
  have hML : M * L * τ < 1 := by
    calc
      _ ≤ M * L * (1 / (2 * q)) := mul_le_mul_of_nonneg_left hτq (by positivity)
      _ < 1 := by rw [mul_one_div, div_lt_iff₀ (by positivity)]; dsimp [q]; nlinarith
  let T : NNReal := ⟨τ, hτ.le⟩
  refine ⟨τ, hτ, hτ₁, fun x hx ↦ ?_⟩
  obtain ⟨u, hu, _⟩ := existsUnique_nonlinearVolterraPath A hA F hF T hM hB hC.le hL.le
    (show 0 ≤ R by dsimp [R]; positivity)
    (fun t ht ↦ hAb t ⟨ht.1, ht.2.trans hτ₁⟩) hCb hLb
    (show M * B + M * C * T ≤ R by change M * B + M * C * τ ≤ M * B + 1; linarith) hML hx
  have hm (t : ℝ) (ht : t ∈ Icc 0 τ) : C0Semigroup.extendTimePath u t =
      A t x + ∫ r in 0..t, A (t - r) (F (C0Semigroup.extendTimePath u r)) := by
    exact (C0Semigroup.extendTimePath_coe u ⟨t, ht⟩).trans (hu.2 ⟨t, ht⟩)
  refine ⟨C0Semigroup.extendTimePath u, C0Semigroup.continuous_extendTimePath u,
    ?_, fun t ↦ (u.norm_coe_le_norm _).trans hu.1, hm⟩
  simpa [hA₀] using hm 0 ⟨le_rfl, hτ.le⟩

end

end Planarwave
