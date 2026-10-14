/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupSector
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Linear

@[expose] public section

/-!
# Semigroups on complex time rays

An analytic semigroup restricted to a ray inside its time sector is again a
strongly continuous semigroup. Its generator is the original generator multiplied
by the ray direction, with exactly the same domain. This is the rotation step in
the sectorial resolvent theory underlying the spectral-to-growth result used in
Section 2 of the paper.
-/

open Filter Set Topology Planarwave

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Restriction of a holomorphic semigroup to a ray, with the identity at its vertex. -/
def rayOperator (G : ℂ → (E →L[ℂ] E)) (ζ : ℂ) (t : NNReal) : E →L[ℂ] E :=
  if t = 0 then ContinuousLinearMap.id ℂ E else G ((t : ℂ) * ζ)

omit [CompleteSpace E] in
@[simp]
theorem rayOperator_zero (G : ℂ → (E →L[ℂ] E)) (ζ : ℂ) :
    rayOperator G ζ 0 = ContinuousLinearMap.id ℂ E := by simp [rayOperator]

omit [CompleteSpace E] in
theorem rayOperator_of_pos (G : ℂ → (E →L[ℂ] E)) (ζ : ℂ)
    {t : NNReal} (ht : 0 < t) : rayOperator G ζ t = G ((t : ℂ) * ζ) := by
  simp [rayOperator, ne_of_gt ht]

omit [CompleteSpace E] in
theorem continuous_rayOperator_apply {η : ℝ} {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η) (x : E) :
    Continuous (fun t : NNReal ↦ rayOperator G ζ t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun s : NNReal ↦ (s : ℂ) * ζ) := by fun_prop
  by_cases ht : t = 0
  · subst t
    rw [continuousAt_iff_punctured_nhds]
    have hray : Tendsto (fun s : NNReal ↦ (s : ℂ) * ζ) (𝓝[≠] 0)
        (𝓝[complexTimeSector η] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hspos : 0 < s := pos_iff_ne_zero.mpr (by simpa using hs)
        exact real_mul_mem_complexTimeSector hζ (show 0 < (s : ℝ) from hspos)
    have hh := (hzero x).comp hray
    simp only [rayOperator_zero, ContinuousLinearMap.id_apply]
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [rayOperator, show s ≠ 0 by simpa using hs]
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    have hz := real_mul_mem_complexTimeSector hζ (show 0 < (t : ℝ) from htpos)
    have hcont : ContinuousAt (fun s : NNReal ↦ G ((s : ℂ) * ζ) x) t :=
      ((ContinuousLinearMap.apply ℂ E x).continuous.continuousAt.comp
        (hG _ hz).continuousAt).comp (f := fun s : NNReal ↦ (s : ℂ) * ζ) hc.continuousAt
    apply hcont.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds htpos] with s hs
    simp [rayOperator, ne_of_gt (show 0 < s from hs)]

/-- Rotation to any ray strictly inside the time sector. -/
def rotate {η : ℝ} {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hadd : ∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
      G (z + w) = (G z).comp (G w))
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η) : C0Semigroup ℂ E where
  toFun := rayOperator G ζ
  map_zero' := rayOperator_zero G ζ
  map_add' s t := by
    by_cases hs : s = 0
    · subst s; simp
    by_cases ht : t = 0
    · subst t; simp
    have hspos : 0 < s := pos_iff_ne_zero.mpr hs
    have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    rw [rayOperator_of_pos G ζ (add_pos hspos htpos),
      rayOperator_of_pos G ζ hspos, rayOperator_of_pos G ζ htpos]
    push_cast
    rw [add_mul]
    exact hadd _ (real_mul_mem_complexTimeSector hζ (show 0 < (s : ℝ) from hspos))
      _ (real_mul_mem_complexTimeSector hζ (show 0 < (t : ℝ) from htpos))
  strongContinuous' := continuous_rayOperator_apply hG hzero hζ

@[simp]
theorem rotate_apply {η : ℝ} {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hadd : ∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
      G (z + w) = (G z).comp (G w))
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η) (t : NNReal) :
    rotate hG hadd hzero hζ t = rayOperator G ζ t := rfl

/-- Interior complex-time smoothing identifies the original generator with the
complex time derivative. No operator-norm continuity at zero is needed. -/
theorem hasGeneratorAt_holomorphicSectorExtension (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    {z : ℂ} (hz : z ∈ complexTimeSector η) (x : E) :
    S.HasGeneratorAt (G z x) (deriv G z x) := by
  have hd : HasDerivAt (fun w ↦ G w x) (deriv G z x) z := by
    simpa using ((hG z hz).differentiableAt.hasDerivAt.clm_apply (hasDerivAt_const z x))
  have hshift := hd.scomp_of_eq 0 (Complex.ofRealCLM.hasDerivAt.const_add z)
    (by simp)
  have hshift' : HasDerivAt (fun t : ℝ ↦ G (z + (t : ℂ)) x) (deriv G z x) 0 := by
    simpa using! hshift
  apply hshift'.hasDerivWithinAt.congr
  · intro t ht
    rw [S.holomorphicSectorExtension_add_real hη hG hreal hz ht]
    have hcomm := S.holomorphicSectorExtension_comp_comm hη hG hreal (S t.toNNReal)
      (fun s ↦ S.commute s t.toNNReal) hz
    exact congrArg (fun A : E →L[ℂ] E ↦ A x) hcomm.symm
  · simp

/-- Interior complex times also lie in the rotated generator domain. -/
theorem rotate_hasGeneratorAt_extension {η : ℝ} {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hadd : ∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
      G (z + w) = (G z).comp (G w))
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η)
    {z : ℂ} (hz : z ∈ complexTimeSector η) (x : E) :
    (rotate hG hadd hzero hζ).HasGeneratorAt (G z x) (ζ • deriv G z x) := by
  have hd : HasDerivAt (fun w ↦ G w x) (deriv G z x) z := by
    simpa using ((hG z hz).differentiableAt.hasDerivAt.clm_apply (hasDerivAt_const z x))
  have hshift := hd.scomp_of_eq 0
    ((Complex.ofRealCLM.hasDerivAt.mul_const ζ).add_const z) (by simp)
  have hshift' : HasDerivAt (fun t : ℝ ↦ G ((t : ℂ) * ζ + z) x)
      (ζ • deriv G z x) 0 := by simpa using! hshift
  apply hshift'.hasDerivWithinAt.congr
  · intro t ht
    by_cases ht₀ : t = 0
    · subst t; simp [realOrbit]
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht₀)
    have htNN : 0 < t.toNNReal := Real.toNNReal_pos.mpr htpos
    simp only [realOrbit, rotate_apply, rayOperator_of_pos G ζ htNN,
      Real.coe_toNNReal _ ht, hadd _ (real_mul_mem_complexTimeSector hζ htpos) _ hz,
      ContinuousLinearMap.comp_apply]
  · simp [realOrbit]

/-- A bounded operator commuting with the semigroup preserves its full generator graph. -/
theorem HasGeneratorAt.map_of_comp_comm {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) (B : E →L[ℂ] E)
    (hcomm : ∀ t : NNReal, (S t).comp B = B.comp (S t)) :
    S.HasGeneratorAt (B x) (B y) := by
  have hd := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 h
  change HasDerivWithinAt (fun t ↦ B (S.realOrbit x t)) (B y) (Ici 0) 0 at hd
  apply hd.congr
  · intro t _
    exact congrArg (fun A : E →L[ℂ] E ↦ A x) (hcomm t.toNNReal)
  · simp

/-- Rotation multiplies the generator by the direction of the ray. The proof
passes through positive complex times and then closes the generator graph. -/
theorem HasGeneratorAt.rotate {S : C0Semigroup ℂ E} {x y : E}
    (h : S.HasGeneratorAt x y) {η : ℝ} (hη : 0 < η)
    {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η) :
    (C0Semigroup.rotate hG (fun _ hz _ hw ↦ S.holomorphicSectorExtension_add hη hG hreal hz hw)
      hzero hζ).HasGeneratorAt x (ζ • y) := by
  have hadd : ∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
      G (z + w) = (G z).comp (G w) :=
    fun _ hz _ hw ↦ S.holomorphicSectorExtension_add hη hG hreal hz hw
  let T := C0Semigroup.rotate hG hadd hzero hζ
  have hlim : Tendsto (fun t : NNReal ↦ (T t x, ζ • T t y)) (𝓝[≠] 0)
      (𝓝 (x, ζ • y)) :=
    ((T.tendsto_zero x).prodMk_nhds ((T.tendsto_zero y).const_smul ζ)).mono_left nhdsWithin_le_nhds
  apply T.isClosed_generatorGraph.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := pos_iff_ne_zero.mpr (by simpa using ht)
  have hz := real_mul_mem_complexTimeSector hζ (show 0 < (t : ℝ) from htpos)
  have hcomm : ∀ s : NNReal, (S s).comp (G ((t : ℂ) * ζ)) =
      (G ((t : ℂ) * ζ)).comp (S s) := fun s ↦
    (S.holomorphicSectorExtension_comp_comm hη hG hreal (S s)
      (fun r ↦ S.commute r s) hz).symm
  have hderiv := (S.hasGeneratorAt_holomorphicSectorExtension hη hG hreal hz x).unique
    (h.map_of_comp_comm _ hcomm)
  have hrot := rotate_hasGeneratorAt_extension hG hadd hzero hζ hz x
  rw [hderiv] at hrot
  simpa only [T, rotate_apply, rayOperator_of_pos G ζ htpos] using hrot

/-- Rotation preserves the generator domain exactly, including the converse
inclusion. This prevents an unnoticed enlargement of the closed operator domain. -/
theorem rotate_hasGeneratorAt_iff (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η) (x y : E) :
    (rotate hG (fun _ hz _ hw ↦ S.holomorphicSectorExtension_add hη hG hreal hz hw)
      hzero hζ).HasGeneratorAt x y ↔ S.HasGeneratorAt x (ζ⁻¹ • y) := by
  have hζ₀ : ζ ≠ 0 := by intro h; simpa [h] using hζ.1
  have hadd : ∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
      G (z + w) = (G z).comp (G w) :=
    fun _ hz _ hw ↦ S.holomorphicSectorExtension_add hη hG hreal hz hw
  let T := rotate hG hadd hzero hζ
  constructor
  · intro h
    have hlim : Tendsto (fun t : NNReal ↦ (T t x, ζ⁻¹ • T t y)) (𝓝[≠] 0)
        (𝓝 (x, ζ⁻¹ • y)) :=
      ((T.tendsto_zero x).prodMk_nhds ((T.tendsto_zero y).const_smul ζ⁻¹)).mono_left nhdsWithin_le_nhds
    apply S.isClosed_generatorGraph.mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := pos_iff_ne_zero.mpr (by simpa using ht)
    have hz := real_mul_mem_complexTimeSector hζ (show 0 < (t : ℝ) from htpos)
    have hrot := rotate_hasGeneratorAt_extension hG hadd hzero hζ hz x
    have happly : T.HasGeneratorAt (G ((t : ℂ) * ζ) x) (T t y) := by
      simpa only [T, rotate_apply, rayOperator_of_pos G ζ htpos] using h.apply t
    have heq : ζ⁻¹ • T t y = deriv G ((t : ℂ) * ζ) x := by
      rw [← hrot.unique happly, smul_smul, inv_mul_cancel₀ hζ₀, one_smul]
    change S.HasGeneratorAt (T t x) (ζ⁻¹ • T t y)
    rw [heq]
    simpa only [T, rotate_apply, rayOperator_of_pos G ζ htpos] using
      S.hasGeneratorAt_holomorphicSectorExtension hη hG hreal hz x
  · intro h
    simpa only [smul_smul, mul_inv_cancel₀ hζ₀, one_smul] using
      h.rotate hη hG hreal hzero hζ

/-- A sector bound restricts to an exponential bound on each rotated semigroup. -/
theorem norm_rotate_le {η M ω : ℝ} (hM : 1 ≤ M)
    {G : ℂ → (E →L[ℂ] E)} (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hadd : ∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
      G (z + w) = (G z).comp (G w))
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    (hbound : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η) (t : NNReal) :
    ‖rotate hG hadd hzero hζ t‖ ≤ M * Real.exp ((ω * ‖ζ‖) * t) := by
  by_cases ht : t = 0
  · subst t
    simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E)).trans hM
  have htpos : 0 < t := pos_iff_ne_zero.mpr ht
  rw [rotate_apply, rayOperator_of_pos G ζ htpos]
  have hb := hbound _ (real_mul_mem_complexTimeSector hζ (show 0 < (t : ℝ) from htpos))
  simpa only [norm_mul, Complex.norm_real, NNReal.norm_eq, mul_left_comm, mul_comm,
    mul_assoc] using hb

end

end C0Semigroup
