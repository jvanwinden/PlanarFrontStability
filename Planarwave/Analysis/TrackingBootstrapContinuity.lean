/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

@[expose] public section

/-!
# The continuity argument closing the tracking bootstrap

The bootstrap functional in the paper is a running supremum of a continuous
scalar quantity. Its continuity, including at the initial time, permits the
final improvement argument in Lemma `key`: a bound by one improves to a bound
by one half, and consequently persists throughout the interval. No monotonicity
assumption is needed for this last topological step.
-/

namespace Planarwave

open Set

/-- The running supremum used in the tracking bootstrap. -/
noncomputable def trackingRunningSup (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup (q '' Icc 0 t)

@[simp] theorem trackingRunningSup_zero (q : ℝ → ℝ) :
    trackingRunningSup q 0 = q 0 := by
  simp [trackingRunningSup]

/-- The running supremum controls exactly the preceding initial interval. -/
theorem trackingRunningSup_le_iff {q : ℝ → ℝ} {T t A : ℝ}
    (hq : ContinuousOn q (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    trackingRunningSup q t ≤ A ↔ ∀ s ∈ Icc 0 t, q s ≤ A := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hb := isCompact_Icc.bddAbove_image (hq.mono hsub)
  constructor
  · intro h s hs
    exact (le_csSup hb (mem_image_of_mem q hs)).trans h
  · intro h
    exact csSup_le ((nonempty_Icc.mpr ht.1).image q) (by
      rintro _ ⟨s, hs, rfl⟩
      exact h s hs)

theorem le_trackingRunningSup {q : ℝ → ℝ} {T t s : ℝ}
    (hq : ContinuousOn q (Icc 0 T)) (ht : t ∈ Icc 0 T)
    (hs : s ∈ Icc 0 t) : q s ≤ trackingRunningSup q t :=
  (trackingRunningSup_le_iff hq ht).mp le_rfl s hs

theorem monotoneOn_trackingRunningSup {q : ℝ → ℝ} {T : ℝ}
    (hq : ContinuousOn q (Icc 0 T)) :
    MonotoneOn (trackingRunningSup q) (Icc 0 T) := by
  intro s hs t ht hst
  exact (trackingRunningSup_le_iff hq hs).mpr fun r hr =>
    le_trackingRunningSup hq ht ⟨hr.1, hr.2.trans hst⟩

/-- Continuity of a running maximum of a continuous real function.

Clamping the spatial parameter to `[0,t]` realizes all these maxima on the
fixed compact interval `[0,T]`, to which continuity of compact maxima applies.
-/
theorem continuousOn_trackingRunningSup {q : ℝ → ℝ} {T : ℝ}
    (hq : ContinuousOn q (Icc 0 T)) :
    ContinuousOn (trackingRunningSup q) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun t : Icc (0 : ℝ) T => trackingRunningSup q t.1)
  let F : Icc (0 : ℝ) T → ℝ → ℝ := fun t s => q (max 0 (min t.1 s))
  have hF : Continuous ↿F := by
    apply hq.comp_continuous
    · exact continuous_const.max ((continuous_subtype_val.comp continuous_fst).min
        continuous_snd)
    · intro p
      exact ⟨le_max_left _ _, max_le (p.1.property.1.trans p.1.property.2)
        ((min_le_left _ _).trans p.1.property.2)⟩
  have hc := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).continuous_sSup hF
  have heq (t : Icc (0 : ℝ) T) : F t '' Icc 0 T = q '' Icc 0 t.1 := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨max 0 (min t.1 s), ⟨le_max_left _ _,
        max_le t.property.1 (min_le_left _ _)⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, ⟨hs.1, hs.2.trans t.property.2⟩, ?_⟩
      simp only [F, min_eq_right hs.2, max_eq_right hs.1]
  simpa only [heq, trackingRunningSup, domRestrict_apply] using hc

/-- The paper's final continuity argument, separated from the analytic
estimate supplying the improvement. -/
theorem tracking_bootstrap_of_continuousOn {η : ℝ → ℝ} {T : ℝ}
    (hη : ContinuousOn η (Icc 0 T)) (hzero : η 0 ≤ 1 / 2)
    (himprove : ∀ t ∈ Icc 0 T, η t ≤ 1 → η t ≤ 1 / 2) :
    ∀ t ∈ Icc 0 T, η t ≤ 1 / 2 := by
  intro t ht
  apply himprove t ht
  by_contra h
  have hgt : 1 < η t := lt_of_not_ge h
  have hcont : ContinuousOn η (Icc 0 t) :=
    hη.mono (Icc_subset_Icc le_rfl ht.2)
  obtain ⟨s, hs, hval⟩ := intermediate_value_Icc ht.1 hcont
    (show (1 : ℝ) ∈ Icc (η 0) (η t) from ⟨by linarith, hgt.le⟩)
  have hhalf := himprove s ⟨hs.1, hs.2.trans ht.2⟩ (by linarith)
  linarith

/-- A bootstrap hypothesis over the entire preceding interval can be closed
using precisely the running supremum appearing in the paper. -/
theorem tracking_running_sup_bootstrap {q : ℝ → ℝ} {T : ℝ}
    (hq : ContinuousOn q (Icc 0 T)) (hzero : q 0 ≤ 1 / 2)
    (himprove : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, q s ≤ 1) →
      ∀ s ∈ Icc 0 t, q s ≤ 1 / 2) :
    ∀ t ∈ Icc 0 T, trackingRunningSup q t ≤ 1 / 2 := by
  apply tracking_bootstrap_of_continuousOn (continuousOn_trackingRunningSup hq)
  · simpa using hzero
  · intro t ht hsmall
    exact (trackingRunningSup_le_iff hq ht).mpr
      (himprove t ht ((trackingRunningSup_le_iff hq ht).mp hsmall))

/-- The explicit smallness threshold from the proof of Lemma `key`. -/
theorem tracking_bootstrap_smallness {C : ℝ} (hC : 0 < C) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ M : ℝ, 0 ≤ M → M ≤ δ →
      C * M ^ ((3 : ℝ) / 4) ≤ 1 / 2 := by
  refine ⟨min ((2 * C) ^ (-(4 : ℝ) / 3)) 1, lt_min (by positivity) zero_lt_one,
    min_le_right _ _, ?_⟩
  intro M hM hsmall
  have hp : M ^ ((3 : ℝ) / 4) ≤
      ((2 * C) ^ (-(4 : ℝ) / 3)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hM (hsmall.trans (min_le_left _ _)) (by norm_num)
  apply (mul_le_mul_of_nonneg_left hp hC.le).trans
  rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * C)]
  norm_num only [show (-(4 : ℝ) / 3) * (3 / 4) = -1 by norm_num]
  rw [Real.rpow_neg_one]
  field_simp
  linarith

/-- Linear small-amplitude terms are absorbed by the `M^(3/4)` improvement
when `M ≤ 1`, as in the initial and improved bootstrap estimates. -/
theorem tracking_bootstrap_amplitude_sum {M K C : ℝ}
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (hK : 0 ≤ K) :
    M + K * M + C * M ^ ((3 : ℝ) / 4) ≤
      (1 + K + C) * M ^ ((3 : ℝ) / 4) := by
  have hpow : M ≤ M ^ ((3 : ℝ) / 4) :=
    Real.self_le_rpow_of_le_one hM hM1 (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hpow hK]

section Template

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The quantity inside the supremum in equation `template` of the paper. -/
noncomputable def trackingBootstrapTemplate (M : ℝ) (σ : ℝ → E) (N : ℝ → F)
    (t : ℝ) : ℝ :=
  M + ‖σ t‖ + M⁻¹ * (1 + t) ^ ((5 : ℝ) / 4) * ‖N t‖

/-- The paper's bootstrap functional `η`. -/
noncomputable def trackingBootstrapFunctional (M : ℝ) (σ : ℝ → E) (N : ℝ → F)
    (t : ℝ) : ℝ :=
  trackingRunningSup (trackingBootstrapTemplate M σ N) t

theorem continuousOn_trackingBootstrapTemplate {σ : ℝ → E} {N : ℝ → F} {T M : ℝ}
    (hσ : ContinuousOn σ (Icc 0 T)) (hN : ContinuousOn N (Icc 0 T)) :
    ContinuousOn (trackingBootstrapTemplate M σ N) (Icc 0 T) := by
  exact (continuousOn_const.add hσ.norm).add
    ((continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const
      (fun _ _ => Or.inr (by norm_num)))).mul hN.norm)

theorem continuousOn_trackingBootstrapFunctional {σ : ℝ → E} {N : ℝ → F} {T M : ℝ}
    (hσ : ContinuousOn σ (Icc 0 T)) (hN : ContinuousOn N (Icc 0 T)) :
    ContinuousOn (trackingBootstrapFunctional M σ N) (Icc 0 T) :=
  continuousOn_trackingRunningSup (continuousOn_trackingBootstrapTemplate hσ hN)

@[simp] theorem trackingBootstrapFunctional_zero (M : ℝ) (σ : ℝ → E) (N : ℝ → F) :
    trackingBootstrapFunctional M σ N 0 = M + ‖σ 0‖ + M⁻¹ * ‖N 0‖ := by
  simp [trackingBootstrapFunctional, trackingBootstrapTemplate]

/-- Unpacking the bootstrap gives precisely the phase and source bounds
used as the starting point of Lemma `key`. The amplitude is positive here;
the zero-amplitude solution is handled separately. -/
theorem trackingBootstrapFunctional_le_one_bounds
    {σ : ℝ → E} {N : ℝ → F} {T M t : ℝ}
    (hσ : ContinuousOn σ (Icc 0 T)) (hN : ContinuousOn N (Icc 0 T))
    (hM : 0 < M) (ht : t ∈ Icc 0 T)
    (hη : trackingBootstrapFunctional M σ N t ≤ 1) :
    M ≤ 1 ∧ ∀ s ∈ Icc 0 t, ‖σ s‖ ≤ 1 ∧
      ‖N s‖ ≤ M * (1 + s) ^ (-(5 : ℝ) / 4) := by
  have hpoint := (trackingRunningSup_le_iff
    (continuousOn_trackingBootstrapTemplate hσ hN) ht).mp hη
  have hw (s : ℝ) (hs : 0 ≤ s) :
      0 ≤ M⁻¹ * (1 + s) ^ ((5 : ℝ) / 4) * ‖N s‖ := by positivity
  refine ⟨?_, ?_⟩
  · have hz := hpoint 0 ⟨le_rfl, ht.1⟩
    dsimp [trackingBootstrapTemplate] at hz
    linarith [norm_nonneg (σ 0), hw 0 le_rfl]
  · intro s hs
    have hb := hpoint s hs
    dsimp [trackingBootstrapTemplate] at hb
    have hbase : 0 < 1 + s := by linarith [hs.1]
    have hpow : 0 < (1 + s) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos hbase _
    have hweight : M⁻¹ * (1 + s) ^ ((5 : ℝ) / 4) * ‖N s‖ ≤ 1 := by
      linarith [norm_nonneg (σ s)]
    refine ⟨by linarith [hw s hs.1], ?_⟩
    have hmul : (1 + s) ^ ((5 : ℝ) / 4) * ‖N s‖ ≤ M := by
      have := mul_le_mul_of_nonneg_left hweight hM.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul, mul_one] using this
    calc
      ‖N s‖ ≤ M / (1 + s) ^ ((5 : ℝ) / 4) :=
        (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hmul)
      _ = M * (1 + s) ^ (-(5 : ℝ) / 4) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hbase.le]
        congr 2
        ring

/-- Combining the improved phase and source estimates gives the paper's
`η ≤ C M^(3/4)` bound. The real-power cancellations keep the source weight
exactly `(1+s)^(5/4)`, without changing the bootstrap functional. -/
theorem trackingBootstrapFunctional_improved
    {σ : ℝ → E} {N : ℝ → F} {T M t K A : ℝ}
    (hσ : ContinuousOn σ (Icc 0 T)) (hN : ContinuousOn N (Icc 0 T))
    (hM : 0 < M) (hM1 : M ≤ 1) (hK : 0 ≤ K) (ht : t ∈ Icc 0 T)
    (hphase : ∀ s ∈ Icc 0 t, ‖σ s‖ ≤ K * M)
    (hsource : ∀ s ∈ Icc 0 t,
      ‖N s‖ ≤ A * M ^ ((7 : ℝ) / 4) * (1 + s) ^ (-(5 : ℝ) / 4)) :
    trackingBootstrapFunctional M σ N t ≤
      (1 + K + A) * M ^ ((3 : ℝ) / 4) := by
  apply (trackingRunningSup_le_iff
    (continuousOn_trackingBootstrapTemplate hσ hN) ht).mpr
  intro s hs
  have hbase : 0 < 1 + s := by linarith [hs.1]
  have hMpow : M⁻¹ * M ^ ((7 : ℝ) / 4) = M ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hM]
    norm_num
  have htpow : (1 + s) ^ ((5 : ℝ) / 4) * (1 + s) ^ (-(5 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hbase]
    norm_num
  have hweight : M⁻¹ * (1 + s) ^ ((5 : ℝ) / 4) * ‖N s‖ ≤
      A * M ^ ((3 : ℝ) / 4) := by
    calc
      _ ≤ M⁻¹ * (1 + s) ^ ((5 : ℝ) / 4) *
          (A * M ^ ((7 : ℝ) / 4) * (1 + s) ^ (-(5 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (hsource s hs) (by positivity)
      _ = A * (M⁻¹ * M ^ ((7 : ℝ) / 4)) *
          ((1 + s) ^ ((5 : ℝ) / 4) * (1 + s) ^ (-(5 : ℝ) / 4)) := by ring
      _ = _ := by rw [hMpow, htpow, mul_one]
  exact (add_le_add (add_le_add le_rfl (hphase s hs)) hweight).trans
    (tracking_bootstrap_amplitude_sum hM.le hM1 hK)

/-- The quadratic initial source estimate gives the linear initial bound
for `η`, before it is absorbed in the three-quarter-power estimate. -/
theorem trackingBootstrapFunctional_zero_le {M A : ℝ}
    (σ : ℝ → E) (N : ℝ → F) (hM : 0 < M) (hσ : σ 0 = 0)
    (hN : ‖N 0‖ ≤ A * M ^ 2) :
    trackingBootstrapFunctional M σ N 0 ≤ (1 + A) * M := by
  rw [trackingBootstrapFunctional_zero, hσ, norm_zero, add_zero]
  calc
    M + M⁻¹ * ‖N 0‖ ≤ M + M⁻¹ * (A * M ^ 2) := by
      gcongr
    _ = (1 + A) * M := by field_simp

end Template

end Planarwave
