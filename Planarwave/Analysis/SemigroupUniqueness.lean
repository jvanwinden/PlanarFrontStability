/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupDuhamel
public import Planarwave.Analysis.SemigroupGeneratorDensity

@[expose] public section

/-!
# A strongly continuous semigroup is determined by its generator

Strong joint continuity suffices for the product differentiation used here; no operator-norm
continuity at zero is assumed. Differentiating `T(t-r) S(r)x` on generator-domain vectors and
then using density proves uniqueness. This justifies the reassociation of bounded perturbations
in the compact-family argument from the paper's appendix.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Differentiating a strongly continuous operator action on a differentiable moving vector.
Only the fixed-vector time derivative, not an operator-norm derivative, is needed. -/
theorem hasDerivAt_realOrbit_apply (S : C0Semigroup ℂ E) {a : ℝ → ℝ} {u : ℝ → E}
    {r : ℝ} {u' v' : E} (ha : ContinuousAt a r) (hu : HasDerivAt u u' r)
    (hv : HasDerivAt (fun s ↦ S.realOrbit (u r) (a s)) v' r) :
    HasDerivAt (fun s ↦ S.realOrbit (u s) (a s)) (S.realOrbit u' (a r) + v') r := by
  have hp : Tendsto (fun s ↦ (a s, slope u r s)) (𝓝[≠] r) (𝓝 (a r, u')) := by
    simpa only [nhds_prod_eq] using
      (ha.tendsto.mono_left nhdsWithin_le_nhds).prodMk hu.tendsto_slope
  have hlim : Tendsto (fun s ↦ S.realOrbit (slope u r s) (a s)) (𝓝[≠] r)
      (𝓝 (S.realOrbit u' (a r))) := by
    exact S.continuous_realOrbit_joint.continuousAt.tendsto.comp hp
  rw [hasDerivAt_iff_tendsto_slope]
  apply (hlim.add hv.tendsto_slope).congr'
  apply Eventually.of_forall
  intro s
  simp only [slope, vsub_eq_sub, realOrbit]
  have hsmul : S (a s).toNNReal ((s - r)⁻¹ • (u s - u r)) =
      (s - r)⁻¹ • S (a s).toNNReal (u s - u r) :=
    ((S (a s).toNNReal).restrictScalars ℝ).map_smul _ _
  rw [hsmul]
  simp only [_root_.map_sub, ← smul_add, sub_add_sub_cancel]

/-- Inclusion of generator graphs forces equality of the two semigroups. -/
theorem eq_of_generator_le (S T : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y → T.HasGeneratorAt x y) : S = T := by
  have honDomain (t : NNReal) {x y : E} (hx : S.HasGeneratorAt x y) : S t x = T t x := by
    let F : ℝ → E := fun r ↦ T.realOrbit (S.realOrbit x r) ((t : ℝ) - r)
    have hc : Continuous F := T.continuous_realOrbit_joint.comp
      ((continuous_const.sub continuous_id).prodMk (S.continuous_realOrbit x))
    have hd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (t : ℝ)) : HasDerivAt F 0 r := by
      have hpair : T.HasGeneratorAt (S.realOrbit x r) (S.realOrbit y r) :=
        hgen _ _ (hx.apply r.toNNReal)
      have hfixed := (hpair.hasDerivAt (sub_pos.mpr hr.2)).scomp_of_eq r
        ((hasDerivAt_id r).const_sub (t : ℝ)) (by rfl)
      have hd := T.hasDerivAt_realOrbit_apply
        (a := fun s : ℝ ↦ (t : ℝ) - s)
        (u := S.realOrbit x) (by fun_prop) (hx.hasDerivAt hr.1) hfixed
      simpa only [neg_smul, one_smul, add_neg_cancel] using! hd
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.2 hc.continuousOn hd
      (intervalIntegrable_const (c := (0 : E)))
    have heq : F t = F 0 := sub_eq_zero.mp (by simpa only [intervalIntegral.integral_zero] using! hi.symm)
    simpa [F] using heq
  ext t x
  have heq := Continuous.ext_on S.dense_generatorDomain (S t).continuous (T t).continuous (by
    rintro z ⟨y, hy⟩
    exact honDomain t hy)
  exact congrFun heq x

/-- In particular equality of the full generator relations determines the semigroup. -/
theorem eq_of_generator_iff (S T : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ T.HasGeneratorAt x y) : S = T :=
  S.eq_of_generator_le T (fun x y ↦ (hgen x y).mp)

end

end C0Semigroup
