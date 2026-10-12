/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Duhamel's integral on finite time intervals

The bounded-perturbation theorem used twice in Lemma 2.2 is based on the Volterra equation
`u(t) = S(t)x + ∫₀ᵗ S(t-r) B u(r) dr`. We construct its integral operator on continuous paths,
prove the small-time norm bound, and solve the equation by the Banach-algebra Neumann theorem.
The integrals are taken along strongly continuous orbits, not in the operator norm topology.
-/

open Filter MeasureTheory Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Strong continuity and local operator bounds imply joint continuity of the action. -/
theorem continuous_realOrbit_joint (S : C0Semigroup ℂ E) :
    Continuous (fun p : ℝ × E ↦ S.realOrbit p.2 p.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  let T : NNReal := t.toNNReal + 1
  obtain ⟨M, hM, hbound⟩ := S.exists_local_bound T
  have hM₀ : 0 ≤ M := le_trans zero_le_one hM
  have hc : ContinuousOn (fun p : ℝ × E ↦ S.realOrbit p.2 p.1)
      (Iic (T : ℝ) ×ˢ univ) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ ⟨M, hM₀⟩
    · intro r hr
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le
        (K := ⟨M, hM₀⟩)
        (hbound r.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hr))).lipschitzOnWith
    · intro y _
      exact (S.continuous_realOrbit y).continuousOn
  apply hc.continuousAt
  rw [prod_mem_nhds_iff]
  refine ⟨Iic_mem_nhds ?_, univ_mem⟩
  have ht : t ≤ (t.toNNReal : ℝ) := Real.le_coe_toNNReal t
  change t < (t.toNNReal : ℝ) + 1
  linarith

/-- Duhamel's time convolution, expressed using the real-time orbit extension. -/
def duhamel (S : C0Semigroup ℂ E) (f : ℝ → E) (t : ℝ) : E :=
  ∫ r in 0..t, S.realOrbit (f r) (t - r)

@[simp]
theorem duhamel_zero (S : C0Semigroup ℂ E) (f : ℝ → E) : S.duhamel f 0 = 0 := by
  simp [duhamel]

theorem continuous_duhamel_integrand (S : C0Semigroup ℂ E) {f : ℝ → E} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ ↦ S.realOrbit (f p.2) (p.1 - p.2)) :=
  S.continuous_realOrbit_joint.comp
    ((continuous_fst.sub continuous_snd).prodMk (hf.comp continuous_snd))

/-- Continuous forcing gives a continuous Duhamel orbit, including time zero. -/
theorem continuous_duhamel (S : C0Semigroup ℂ E) {f : ℝ → E} (hf : Continuous f) :
    Continuous (S.duhamel f) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (S.continuous_duhamel_integrand hf) continuous_id

theorem duhamel_add (S : C0Semigroup ℂ E) {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    S.duhamel (f + g) t = S.duhamel f t + S.duhamel g t := by
  simp only [duhamel, Pi.add_apply, realOrbit, _root_.map_add]
  have hcf : Continuous fun r : ℝ ↦ S.realOrbit (f r) (t - r) :=
    (S.continuous_duhamel_integrand hf).comp (continuous_const.prodMk continuous_id)
  have hcg : Continuous fun r : ℝ ↦ S.realOrbit (g r) (t - r) :=
    (S.continuous_duhamel_integrand hg).comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_add
    (hcf.intervalIntegrable 0 t) (hcg.intervalIntegrable 0 t)

theorem duhamel_smul (S : C0Semigroup ℂ E) (a : ℂ) (f : ℝ → E) (t : ℝ) :
    S.duhamel (a • f) t = a • S.duhamel f t := by
  simp only [duhamel, Pi.smul_apply, realOrbit, map_smul, intervalIntegral.integral_smul]

/-- A local operator bound yields the Volterra estimate with its small time factor. -/
theorem norm_duhamel_le (S : C0Semigroup ℂ E) (T : NNReal) {M C : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r : NNReal, r ≤ T → ‖S r‖ ≤ M) (f : ℝ → E)
    (hf : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖f r‖ ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ (T : ℝ)) : ‖S.duhamel f t‖ ≤ M * C * t := by
  have hb : ∀ r ∈ uIoc (0 : ℝ) t, ‖S.realOrbit (f r) (t - r)‖ ≤ M * C := by
    intro r hr
    have hr' : r ∈ Ioc (0 : ℝ) t := uIoc_of_le ht ▸ hr
    have ht' : (t - r).toNNReal ≤ T :=
      Real.toNNReal_le_iff_le_coe.mpr (by linarith [hr'.1])
    exact ((S (t - r).toNNReal).le_opNorm (f r)).trans
      (mul_le_mul (hbound _ ht') (hf r ⟨hr'.1.le, hr'.2.trans htT⟩) (norm_nonneg _) hM)
  simpa only [duhamel, sub_zero, abs_of_nonneg ht] using!
    intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- Continuous paths on a compact nonnegative time interval, with the supremum norm. -/
abbrev TimePath (T : NNReal) := C(Icc (0 : ℝ) (T : ℝ), E)

/-- Constant extension outside a path's time interval, used only to write ordinary integrals. -/
def extendTimePath {T : NNReal} (u : TimePath (E := E) T) (r : ℝ) : E :=
  u (projIcc 0 (T : ℝ) T.2 r)

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem continuous_extendTimePath {T : NNReal} (u : TimePath (E := E) T) :
    Continuous (extendTimePath u) := u.continuous.comp continuous_projIcc

omit [NormedSpace ℂ E] [CompleteSpace E] in
@[simp]
theorem extendTimePath_coe {T : NNReal} (u : TimePath (E := E) T)
    (t : Icc (0 : ℝ) (T : ℝ)) : extendTimePath u t = u t := by
  simp [extendTimePath, projIcc, t.2.1, t.2.2]

/-- The bounded-coefficient Volterra term as a continuous path. -/
def perturbationPath (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (u : TimePath (E := E) T) : TimePath (E := E) T where
  toFun t := S.duhamel (fun r ↦ B (extendTimePath u r)) t
  continuous_toFun := (S.continuous_duhamel
    (B.continuous.comp (continuous_extendTimePath u))).comp continuous_subtype_val

/-- The path-space norm bound is uniform in the continuous path. -/
theorem norm_perturbationPath_le (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ r : NNReal, r ≤ T → ‖S r‖ ≤ M)
    (u : TimePath (E := E) T) : ‖S.perturbationPath B T u‖ ≤ M * ‖B‖ * T * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    ‖S.perturbationPath B T u t‖ ≤ M * (‖B‖ * ‖u‖) * (t : ℝ) :=
      S.norm_duhamel_le T hM hbound _ (fun r _ ↦
        (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (norm_nonneg B)))
        t.2.1 t.2.2
    _ ≤ M * (‖B‖ * ‖u‖) * (T : ℝ) := by gcongr; exact t.2.2
    _ = M * ‖B‖ * T * ‖u‖ := by ring

/-- The Volterra term is linear in the path. -/
theorem perturbationPath_add (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (u v : TimePath (E := E) T) :
    S.perturbationPath B T (u + v) = S.perturbationPath B T u + S.perturbationPath B T v := by
  ext t
  change S.duhamel (fun r ↦ B (extendTimePath (u + v) r)) t =
    S.duhamel (fun r ↦ B (extendTimePath u r)) t + S.duhamel (fun r ↦ B (extendTimePath v r)) t
  simpa only [extendTimePath, ContinuousMap.add_apply, _root_.map_add, Pi.add_def,
    Function.comp_def] using!
    S.duhamel_add (B.continuous.comp (continuous_extendTimePath u))
      (B.continuous.comp (continuous_extendTimePath v)) t

theorem perturbationPath_smul (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (a : ℂ) (u : TimePath (E := E) T) :
    S.perturbationPath B T (a • u) = a • S.perturbationPath B T u := by
  ext t
  change S.duhamel (fun r ↦ B (extendTimePath (a • u) r)) t =
    a • S.duhamel (fun r ↦ B (extendTimePath u r)) t
  simpa only [extendTimePath, ContinuousMap.smul_apply, map_smul, Pi.smul_apply] using!
    S.duhamel_smul a (fun r ↦ B (extendTimePath u r)) t

/-- The Volterra integral operator on the Banach space of continuous paths. -/
def perturbationOperator (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal) :
    TimePath (E := E) T →L[ℂ] TimePath (E := E) T := by
  let M := (S.exists_local_bound T).choose
  have hM := (S.exists_local_bound T).choose_spec
  exact LinearMap.mkContinuous
    { toFun := S.perturbationPath B T
      map_add' := S.perturbationPath_add B T
      map_smul' := S.perturbationPath_smul B T }
    (M * ‖B‖ * (T : ℝ))
    (S.norm_perturbationPath_le B T (zero_le_one.trans hM.1) hM.2)

@[simp]
theorem perturbationOperator_apply (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    (u : TimePath (E := E) T) : S.perturbationOperator B T u = S.perturbationPath B T u := rfl

/-- The small-time operator norm estimate used to invert the Volterra equation. -/
theorem norm_perturbationOperator_le (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) (T : NNReal)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ r : NNReal, r ≤ T → ‖S r‖ ≤ M) :
    ‖S.perturbationOperator B T‖ ≤ M * ‖B‖ * T := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact S.norm_perturbationPath_le B T hM hbound

/-- The unperturbed path starting at a given initial value. -/
def freePath (S : C0Semigroup ℂ E) (T : NNReal) (x : E) : TimePath (E := E) T where
  toFun t := S.realOrbit x t
  continuous_toFun := (S.continuous_realOrbit x).comp continuous_subtype_val

/-- Small-time existence and uniqueness for the bounded-perturbation integral equation. -/
theorem existsUnique_perturbedPath_of_bound (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    (T : NNReal) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ r : NNReal, r ≤ T → ‖S r‖ ≤ M)
    (hsmall : M * ‖B‖ * T < 1) (x : E) :
    ∃! u : TimePath (E := E) T, ∀ t, u t = S.realOrbit x t + S.perturbationPath B T u t := by
  have hnorm : ‖S.perturbationOperator B T‖ < 1 :=
    (S.norm_perturbationOperator_le B T hM hbound).trans_lt hsmall
  have hbij : Function.Bijective
      (1 - S.perturbationOperator B T : TimePath (E := E) T →L[ℂ] TimePath (E := E) T) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one hnorm)
  obtain ⟨u, hu⟩ := hbij.surjective (S.freePath T x)
  refine ⟨u, ?_, ?_⟩
  · intro t
    have h := congrArg (fun v : TimePath (E := E) T ↦ v t) hu
    change u t - S.perturbationPath B T u t = S.realOrbit x t at h
    exact sub_eq_iff_eq_add.mp h
  · intro v hv
    apply hbij.injective
    rw [hu]
    ext t
    change v t - S.perturbationPath B T v t = S.realOrbit x t
    exact sub_eq_iff_eq_add.mpr (hv t)

/-- A positive time interval can be chosen independently of the initial datum. -/
theorem exists_local_perturbedPath (S : C0Semigroup ℂ E) (B : E →L[ℂ] E) :
    ∃ T : NNReal, 0 < T ∧ ∀ x : E, ∃! u : TimePath (E := E) T,
      ∀ t, u t = S.realOrbit x t + S.perturbationPath B T u t := by
  obtain ⟨M, hM, hbound⟩ := S.exists_local_bound 1
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  let a := M * ‖B‖
  have ha : 0 ≤ a := by positivity
  let τ : ℝ := min 1 (1 / (2 * (a + 1)))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let T : NNReal := ⟨τ, hτ.le⟩
  have hT : T ≤ 1 := by
    change min 1 (1 / (2 * (a + 1))) ≤ (1 : ℝ)
    exact min_le_left _ _
  have hsmall : M * ‖B‖ * (T : ℝ) < 1 := by
    calc
      a * τ ≤ a * (1 / (2 * (a + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) ha
      _ < 1 := by
        rw [mul_one_div]
        apply (div_lt_iff₀ (by positivity)).mpr
        linarith
  exact ⟨T, hτ, fun x ↦ S.existsUnique_perturbedPath_of_bound B T hM₀
    (fun r hr ↦ hbound r (hr.trans hT)) hsmall x⟩

end

end C0Semigroup
