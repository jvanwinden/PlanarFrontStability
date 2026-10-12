/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupRotation
public import Planarwave.Analysis.SemigroupClosedOperator

@[expose] public section

/-!
# Sectorial resolvents from analytic semigroups

Apply the Laplace resolvent construction to complex-time rays. The original
operator convention is `A - z I`, so its inverse is minus the ray direction
times the rotated semigroup's Laplace transform at the rotated spectral parameter.
-/

open Filter Set Topology

namespace Planarwave

/-- Choose one of two fixed time rays, according to the sign of the spectral
parameter's imaginary part. Their Laplace half-planes cover a sector complement. -/
theorem exists_tilted_resolvent_ray {η a : ℝ} (ha : 0 < a) (haη : a < η) (z : ℂ) :
    ∃ ζ ∈ complexTimeSector η, ‖ζ‖ ≤ 1 + a ∧
      (ζ * z).re = z.re + a * |z.im| := by
  let b : ℝ := if 0 ≤ z.im then -a else a
  have hb : |b| = a := by
    dsimp only [b]
    split <;> simp [abs_of_pos ha]
  have hbim : -b * z.im = a * |z.im| := by
    dsimp only [b]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  let ζ : ℂ := 1 + (b : ℂ) * Complex.I
  have hre : ζ.re = 1 := by simp [ζ]
  have him : ζ.im = b := by simp [ζ]
  refine ⟨ζ, ⟨by rw [hre]; norm_num, ?_⟩, ?_, ?_⟩
  · simpa only [him, hre, hb, mul_one] using haη
  · calc
      ‖ζ‖ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + a := by simp [hb]
  · rw [Complex.mul_re, hre, him, one_mul]
    linarith [hbim]

end Planarwave

namespace Planarwave.ClosedOperator

noncomputable section

variable {E Dom : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

/-- Laplace inversion along a complex time ray gives a tilted resolvent half-plane. -/
theorem isInResolvent_of_rotated_semigroup_bound (A : ClosedOperator ℂ E Dom)
    (T : C0Semigroup ℂ E) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hgen : ∀ x y, T.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ ζ • A.operator v = y)
    {M ω : ℝ} (hbound : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < (ζ * z).re) : A.IsInResolvent z := by
  have hleft (v : Dom) : T.laplaceResolvent hbound (ζ * z) hz
      (ζ • (z • A.inclusion v - A.operator v)) = A.inclusion v := by
    simpa only [smul_sub, smul_smul] using
      ((hgen _ _).mpr ⟨v, rfl, rfl⟩).laplaceResolvent_apply hbound (ζ * z) hz
  constructor
  · intro v w hvw
    apply A.inclusion_injective
    rw [← hleft v, ← hleft w]
    apply congrArg
    apply congrArg (fun u : E ↦ ζ • u)
    change A.operator v - z • A.inclusion v = A.operator w - z • A.inclusion w at hvw
    simpa only [neg_sub] using congrArg Neg.neg hvw
  · intro x
    obtain ⟨v, hv, hAv⟩ := (hgen _ _).mp
      (T.hasGeneratorAt_laplaceResolvent hbound (ζ * z) hz (-(ζ • x)))
    refine ⟨v, ?_⟩
    change A.operator v - z • A.inclusion v = x
    apply (smul_right_injective E hζ)
    change ζ • (A.operator v - z • A.inclusion v) = ζ • x
    rw [smul_sub, smul_smul, hAv, hv]
    abel

/-- The fixed-domain inverse is exactly the rotated Laplace transform. -/
theorem ambientResolvent_eq_rotated_laplace (A : ClosedOperator ℂ E Dom)
    (T : C0Semigroup ℂ E) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hgen : ∀ x y, T.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ ζ • A.operator v = y)
    {M ω : ℝ} (hbound : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < (ζ * z).re) :
    A.ambientResolvent z = -(ζ • T.laplaceResolvent hbound (ζ * z) hz) := by
  have hres := A.isInResolvent_of_rotated_semigroup_bound T hζ hgen hbound z hz
  rw [A.ambientResolvent_eq hres]
  apply ContinuousLinearMap.ext
  intro x
  let v := A.resolventInverse z hres x
  have hAv : A.operator v - z • A.inclusion v = x := A.resolventMap_resolventInverse z hres x
  have hleft := ((hgen _ _).mpr ⟨v, rfl, rfl⟩).laplaceResolvent_apply hbound (ζ * z) hz
  have hneg : (ζ * z) • A.inclusion v - ζ • A.operator v = -(ζ • x) := by
    rw [← hAv, smul_sub, smul_smul]
    abel
  rw [hneg, map_neg, map_smul] at hleft
  exact hleft.symm

/-- Quantitative resolvent control in the tilted half-plane. -/
theorem norm_ambientResolvent_le_of_rotated_semigroup_bound (A : ClosedOperator ℂ E Dom)
    (T : C0Semigroup ℂ E) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hgen : ∀ x y, T.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ ζ • A.operator v = y)
    {M ω : ℝ} (hM : 0 ≤ M) (hbound : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t))
    (z : ℂ) (hz : ω < (ζ * z).re) :
    ‖A.ambientResolvent z‖ ≤ ‖ζ‖ * M / ((ζ * z).re - ω) := by
  rw [A.ambientResolvent_eq_rotated_laplace T hζ hgen hbound z hz, norm_neg, norm_smul]
  exact (mul_le_mul_of_nonneg_left (T.norm_laplaceResolvent_le hM hbound (ζ * z) hz)
    (norm_nonneg ζ)).trans_eq (mul_div_assoc _ _ _).symm

/-- Every ray in a bounded holomorphic extension yields an actual resolvent
half-plane, with the expected inverse-distance estimate. -/
theorem resolvent_bound_of_holomorphic_sector (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {η M ω : ℝ} (hη : 0 < η) (hM : 1 ≤ M)
    {G : ℂ → (E →L[ℂ] E)} (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    (hbound : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    {ζ : ℂ} (hζ : ζ ∈ complexTimeSector η) (z : ℂ) (hz : ω * ‖ζ‖ < (ζ * z).re) :
    A.IsInResolvent z ∧ ‖A.ambientResolvent z‖ ≤ ‖ζ‖ * M / ((ζ * z).re - ω * ‖ζ‖) := by
  have hζ₀ : ζ ≠ 0 := by intro h; simpa [h] using hζ.1
  have hadd : ∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
      G (z + w) = (G z).comp (G w) :=
    fun _ hz _ hw ↦ S.holomorphicSectorExtension_add hη hG hreal hz hw
  let T := C0Semigroup.rotate hG hadd hzero hζ
  have hTgen : ∀ x y, T.HasGeneratorAt x y ↔
      ∃ v, A.inclusion v = x ∧ ζ • A.operator v = y := by
    intro x y
    rw [S.rotate_hasGeneratorAt_iff hη hG hreal hzero hζ, hgen]
    constructor
    · rintro ⟨v, hv, hop⟩
      exact ⟨v, hv, by rw [hop, smul_smul, mul_inv_cancel₀ hζ₀, one_smul]⟩
    · rintro ⟨v, hv, hop⟩
      exact ⟨v, hv, by rw [← hop, smul_smul, inv_mul_cancel₀ hζ₀, one_smul]⟩
  have hTb := C0Semigroup.norm_rotate_le hM hG hadd hzero hbound hζ
  exact ⟨A.isInResolvent_of_rotated_semigroup_bound T hζ₀ hTgen hTb z hz,
    A.norm_ambientResolvent_le_of_rotated_semigroup_bound T hζ₀ hTgen (by linarith) hTb z hz⟩

/-- Explicit sectorial enclosure and resolvent bound. The vertex and constants
are uniform whenever the holomorphic extension bound is uniform. -/
theorem resolvent_bound_on_sector_complement (A : ClosedOperator ℂ E Dom)
    (S : C0Semigroup ℂ E)
    (hgen : ∀ x y, S.HasGeneratorAt x y ↔ ∃ v, A.inclusion v = x ∧ A.operator v = y)
    {η a M ω : ℝ} (ha : 0 < a) (haη : a < η) (hM : 1 ≤ M) (hω : 0 ≤ ω)
    {G : ℂ → (E →L[ℂ] E)} (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x))
    (hbound : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (z : ℂ) (hz : ω * (1 + a) < z.re + a * |z.im|) :
    A.IsInResolvent z ∧
      ‖A.ambientResolvent z‖ ≤ (1 + a) * M / (z.re + a * |z.im| - ω * (1 + a)) := by
  obtain ⟨ζ, hζ, hζnorm, hζre⟩ := exists_tilted_resolvent_ray ha haη z
  have hωζ := mul_le_mul_of_nonneg_left hζnorm hω
  have hzrot : ω * ‖ζ‖ < (ζ * z).re := by rw [hζre]; exact hωζ.trans_lt hz
  obtain ⟨hres, hnorm⟩ := A.resolvent_bound_of_holomorphic_sector S hgen (ha.trans haη)
    hM hG hreal hzero hbound hζ z hzrot
  refine ⟨hres, hnorm.trans ?_⟩
  rw [hζre]
  calc
    ‖ζ‖ * M / (z.re + a * |z.im| - ω * ‖ζ‖) ≤
        (1 + a) * M / (z.re + a * |z.im| - ω * ‖ζ‖) := by
      apply div_le_div_of_nonneg_right _ (by rw [hζre] at hzrot; linarith)
      exact mul_le_mul_of_nonneg_right hζnorm (by linarith)
    _ ≤ (1 + a) * M / (z.re + a * |z.im| - ω * (1 + a)) :=
      div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hz) (by linarith)

/-- A leftward spectral wedge cuts every right half-plane in a compact set.
This is the compactness needed to separate the critical eigenvalue from the
rest of the spectrum without ignoring unbounded spectral parameters. -/
theorem isCompact_spectrum_inter_rightHalfPlane (A : ClosedOperator ℂ E Dom)
    {a Ω : ℝ} (ha : 0 < a)
    (hspec : ∀ z ∈ A.spectrum, z.re + a * |z.im| ≤ Ω) (r : ℝ) :
    IsCompact (A.spectrum ∩ {z : ℂ | r ≤ z.re}) := by
  let R := |r| + |Ω| + (|Ω| + |r|) / a
  apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    (A.isClosed_spectrum.inter (isClosed_le continuous_const Complex.continuous_re))
  intro z hz
  have hspecz := hspec z hz.1
  have hre : r ≤ z.re := hz.2
  have hreΩ : z.re ≤ Ω := by nlinarith [abs_nonneg z.im]
  have habsre : |z.re| ≤ |r| + |Ω| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le r, le_abs_self Ω, abs_nonneg r, abs_nonneg Ω]
  have habsim : |z.im| ≤ (|Ω| + |r|) / a := by
    rw [le_div_iff₀ ha]
    nlinarith [le_abs_self Ω, neg_abs_le r]
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add habsre habsim)

end

end Planarwave.ClosedOperator
