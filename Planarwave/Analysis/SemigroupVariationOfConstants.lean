/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupUniqueness

@[expose] public section

/-!
# Variation of constants for classical positive-time solutions

Differentiate the backward orbit `S(t-r) u(r)` and integrate its derivative.
The solution need only belong to the generator domain at positive interior
times. In particular, the initial datum may be an arbitrary BUC function.
This is the classical-to-mild bridge used to identify the inverse-modulated
perturbation with the spatial semigroup response in the paper.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The generator terms cancel in the derivative of the backward orbit.
Only a derivative of a fixed-vector orbit is used; no operator-norm
differentiability of the semigroup is assumed. -/
theorem hasDerivAt_backward_realOrbit (S : C0Semigroup ℂ E)
    {u : ℝ → E} {r t : ℝ} {a f : E} (hrt : r < t)
    (hgen : S.HasGeneratorAt (u r) a) (hu : HasDerivAt u (a + f) r) :
    HasDerivAt (fun s ↦ S.realOrbit (u s) (t - s))
      (S.realOrbit f (t - r)) r := by
  have hfixed := (hgen.hasDerivAt (sub_pos.mpr hrt)).scomp_of_eq r
    ((hasDerivAt_id r).const_sub t) (by rfl)
  have hd := S.hasDerivAt_realOrbit_apply
    (a := fun s : ℝ ↦ t - s) (u := u) (by fun_prop) hu hfixed
  convert! hd using 1
  simp only [neg_smul, one_smul, realOrbit, _root_.map_add]
  abel

/-- A continuous classical solution on a finite interval satisfies Duhamel's
formula. Generator membership and the differential equation are required only
on the positive-time interior, not at either endpoint. -/
theorem eq_realOrbit_add_duhamel_of_hasDerivAt (S : C0Semigroup ℂ E)
    {u a f : ℝ → E} {T t : ℝ}
    (hu : ContinuousOn u (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hgen : ∀ r ∈ Ioo 0 T, S.HasGeneratorAt (u r) (a r))
    (hderiv : ∀ r ∈ Ioo 0 T, HasDerivAt u (a r + f r) r)
    (ht : t ∈ Icc 0 T) :
    u t = S.realOrbit (u 0) t + S.duhamel f t := by
  let v : ℝ → E := fun r ↦ S.realOrbit (u r) (t - r)
  let g : ℝ → E := fun r ↦ S.realOrbit (f r) (t - r)
  have hsubset : Icc (0 : ℝ) t ⊆ Icc 0 T :=
    fun _ hr ↦ ⟨hr.1, hr.2.trans ht.2⟩
  have hv : ContinuousOn v (Icc 0 t) :=
    S.continuous_realOrbit_joint.comp_continuousOn
      ((continuous_const.sub continuous_id).continuousOn.prodMk (hu.mono hsubset))
  have hg : ContinuousOn g (Icc 0 t) :=
    S.continuous_realOrbit_joint.comp_continuousOn
      ((continuous_const.sub continuous_id).continuousOn.prodMk (hf.mono hsubset))
  have hd (r : ℝ) (hr : r ∈ Ioo 0 t) : HasDerivAt v (g r) r := by
    have hrT : r ∈ Ioo 0 T := ⟨hr.1, hr.2.trans_le ht.2⟩
    exact S.hasDerivAt_backward_realOrbit hr.2 (hgen r hrT) (hderiv r hrT)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hv hd
    (hg.intervalIntegrable_of_Icc ht.1)
  have heq : S.duhamel f t = u t - S.realOrbit (u 0) t := by
    simpa only [duhamel, v, g, sub_self, realOrbit_zero, sub_zero] using! hi
  exact (eq_sub_iff_add_eq.mp heq).symm.trans (add_comm _ _)

end

end C0Semigroup
