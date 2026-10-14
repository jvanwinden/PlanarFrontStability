/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.Semigroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The generator relation of a strongly continuous semigroup

The generator is characterized by a right derivative in the ambient Banach norm. The semigroup
law propagates this derivative along each orbit. Integrating the right derivative gives the
usual integral identity and, in turn, two-sided differentiability at positive times.
These facts connect the explicit longitudinal heat construction to the operator in the paper.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The orbit on real time, extended constantly to negative times. -/
def realOrbit (S : C0Semigroup ℂ E) (x : E) (t : ℝ) : E := S t.toNNReal x

@[simp]
theorem realOrbit_coe (S : C0Semigroup ℂ E) (x : E) (t : NNReal) :
    S.realOrbit x (t : ℝ) = S t x := by simp [realOrbit]

@[simp]
theorem realOrbit_zero (S : C0Semigroup ℂ E) (x : E) : S.realOrbit x 0 = x := by
  simp [realOrbit]

theorem continuous_realOrbit (S : C0Semigroup ℂ E) (x : E) : Continuous (S.realOrbit x) :=
  (S.strongContinuous x).comp continuous_real_toNNReal

theorem realOrbit_add (S : C0Semigroup ℂ E) (x : E) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.realOrbit x (s + t) = S s.toNNReal (S.realOrbit x t) := by
  rw [realOrbit, Real.toNNReal_add hs ht, S.add_apply]
  rfl

/-- `y` is the generator of `S` applied to `x`, as a right norm derivative. -/
def HasGeneratorAt (S : C0Semigroup ℂ E) (x y : E) : Prop :=
  HasDerivWithinAt (S.realOrbit x) y (Ici 0) 0

theorem HasGeneratorAt.unique {S : C0Semigroup ℂ E} {x y z : E}
    (h : S.HasGeneratorAt x y) (h' : S.HasGeneratorAt x z) : y = z := by
  exact (h.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (h'.derivWithin (uniqueDiffWithinAt_Ici 0))

/-- The semigroup preserves its generator domain and commutes with the generator there. -/
theorem HasGeneratorAt.apply {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) (t : NNReal) : S.HasGeneratorAt (S t x) (S t y) := by
  have hd := ((S t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 h
  have heq : (fun s : ℝ ↦ S t (S.realOrbit x s)) = S.realOrbit (S t x) := by
    funext s
    simp only [realOrbit, ← S.add_apply, add_comm]
  change HasDerivWithinAt (fun s : ℝ ↦ S t (S.realOrbit x s)) (S t y) (Ici 0) 0 at hd
  rw [heq] at hd
  exact hd

/-- The right derivative at zero propagates to every nonnegative time. -/
theorem HasGeneratorAt.hasDerivWithinAt {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (S.realOrbit x) (S.realOrbit y t) (Ici t) t := by
  have hd := ((S t.toNNReal).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 h
  have hs : MapsTo (fun s : ℝ ↦ s - t) (Ici t) (Ici 0) := by
    intro s hs
    change 0 ≤ s - t
    exact sub_nonneg.mpr hs
  have hshift := hd.scomp_of_eq t ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
    hs (sub_self t).symm
  have hshift' : HasDerivWithinAt
      (fun s : ℝ ↦ S t.toNNReal (S.realOrbit x (s - t))) (S.realOrbit y t) (Ici t) t := by
    simpa only [Function.comp_def, one_smul] using! hshift
  apply hshift'.congr
  · intro s hs
    rw [← S.realOrbit_add x ht (sub_nonneg.mpr hs), add_sub_cancel]
  · simp [realOrbit]

/-- Integral characterization, obtained by integrating the continuous orbit derivative. -/
theorem HasGeneratorAt.integral_eq_sub {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in 0..t, S.realOrbit y r) = S.realOrbit x t - x := by
  simpa only [realOrbit_zero] using
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
      (S.continuous_realOrbit x).continuousOn
      (fun r hr ↦ (h.hasDerivWithinAt hr.1.le).Ioi_of_Ici)
      ((S.continuous_realOrbit y).intervalIntegrable 0 t)

/-- Orbits starting in the generator domain are differentiable at positive times. -/
theorem HasGeneratorAt.hasDerivAt {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (S.realOrbit x) (S.realOrbit y t) t := by
  have hc := S.continuous_realOrbit y
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const x
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  rw [h.integral_eq_sub hr.le, sub_add_cancel]

/-- The integral identity also implies the defining right derivative at zero. -/
theorem hasGeneratorAt_iff_integral_eq_sub (S : C0Semigroup ℂ E) (x y : E) :
    S.HasGeneratorAt x y ↔
      ∀ t : ℝ, 0 ≤ t → (∫ r in 0..t, S.realOrbit y r) = S.realOrbit x t - x := by
  refine ⟨fun h t ht ↦ h.integral_eq_sub ht, ?_⟩
  intro h
  have hc := S.continuous_realOrbit y
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const x
  rw [S.realOrbit_zero] at hd
  apply hd.hasDerivWithinAt.congr
  · intro t ht
    rw [h t ht, sub_add_cancel]
  · simp

/-- Integrating a strongly continuous orbit is a bounded operator, although the semigroup
need not be continuous in operator norm at zero. -/
def orbitIntegralCLM (S : C0Semigroup ℂ E) (t : NNReal) : E →L[ℂ] E := by
  let M := (S.exists_local_bound t).choose
  have hM : ∀ r ≤ t, ‖S r‖ ≤ M := (S.exists_local_bound t).choose_spec.2
  refine LinearMap.mkContinuous
    { toFun := fun x ↦ ∫ r in 0..(t : ℝ), S.realOrbit x r
      map_add' := ?_
      map_smul' := ?_ } (M * (t : ℝ)) ?_
  · intro x y
    simp only [realOrbit, _root_.map_add]
    exact intervalIntegral.integral_add
      ((S.continuous_realOrbit x).intervalIntegrable (μ := volume) _ _)
      ((S.continuous_realOrbit y).intervalIntegrable (μ := volume) _ _)
  · intro a x
    simp only [realOrbit, map_smul, RingHom.id_apply, intervalIntegral.integral_smul]
  · intro x
    have hb : ∀ r ∈ Set.uIoc (0 : ℝ) (t : ℝ), ‖S.realOrbit x r‖ ≤ M * ‖x‖ := by
      intro r hr
      have hrt : r ≤ (t : ℝ) := (uIoc_of_le t.2 ▸ hr).2
      exact ((S r.toNNReal).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hM r.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hrt))
          (norm_nonneg x))
    calc
      ‖∫ r in 0..(t : ℝ), S.realOrbit x r‖ ≤ M * ‖x‖ * |(t : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = (M * (t : ℝ)) * ‖x‖ := by
        simp only [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) from t.2)]
        ring

@[simp]
theorem orbitIntegralCLM_apply (S : C0Semigroup ℂ E) (t : NNReal) (x : E) :
    S.orbitIntegralCLM t x = ∫ r in 0..(t : ℝ), S.realOrbit x r := rfl

/-- The generator graph is closed, by its integral characterization. -/
theorem isClosed_generatorGraph (S : C0Semigroup ℂ E) :
    IsClosed {p : E × E | S.HasGeneratorAt p.1 p.2} := by
  have heq : {p : E × E | S.HasGeneratorAt p.1 p.2} =
      ⋂ t : NNReal, {p : E × E | S.orbitIntegralCLM t p.2 = S t p.1 - p.1} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h t
      simpa [realOrbit] using h.integral_eq_sub (t := (t : ℝ)) t.2
    · intro h
      apply (S.hasGeneratorAt_iff_integral_eq_sub p.1 p.2).mpr
      intro t ht
      have ht' := h ⟨t, ht⟩
      simpa only [orbitIntegralCLM_apply, realOrbit, Real.toNNReal_of_nonneg ht] using! ht'
  rw [heq]
  apply isClosed_iInter
  intro t
  exact isClosed_eq ((S.orbitIntegralCLM t).continuous.comp continuous_snd)
    (((S t).continuous.comp continuous_fst).sub continuous_fst)

/-- A domain containing every positive-time orbit is a core: closing its operator graph
recovers the full semigroup generator graph. This is the graph-norm form of heat regularization. -/
theorem closure_graph_eq_generatorGraph_of_smoothing (S : C0Semigroup ℂ E)
    {Dom : Type*} (inclusion operator : Dom → E)
    (hgen : ∀ v, S.HasGeneratorAt (inclusion v) (operator v))
    (hsmooth : ∀ t : NNReal, 0 < t → ∀ x, ∃ v, inclusion v = S t x) :
    closure (range fun v ↦ (inclusion v, operator v)) =
      {p : E × E | S.HasGeneratorAt p.1 p.2} := by
  apply Subset.antisymm
  · exact closure_minimal (by rintro p ⟨v, rfl⟩; exact hgen v) S.isClosed_generatorGraph
  · intro p hp
    have hlim : Tendsto (fun t : ℝ ↦ (S.realOrbit p.1 t, S.realOrbit p.2 t))
        (𝓝[>] 0) (𝓝 p) := by
      have hc := ((S.continuous_realOrbit p.1).prodMk (S.continuous_realOrbit p.2)).continuousAt
        (x := (0 : ℝ))
      simpa only [realOrbit_zero, Prod.mk.eta] using
        hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    apply isClosed_closure.mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨v, hv⟩ := hsmooth ⟨t, ht.le⟩ ht p.1
    have hvg := hgen v
    rw [hv] at hvg
    have hop := hvg.unique (hp.apply ⟨t, ht.le⟩)
    apply subset_closure
    refine ⟨v, ?_⟩
    simpa only [realOrbit, Real.toNNReal_of_nonneg ht.le] using! Prod.ext hv hop

end

end C0Semigroup
