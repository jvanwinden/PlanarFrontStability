/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-!
# Gluing holomorphic time extensions

Holomorphic extensions from disks centered on the real axis agree on overlaps when
their real restrictions agree. The identity principle then glues the local Taylor
extensions into one holomorphic function on a neighborhood of the positive time axis.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Agreement along the real diameters determines agreement throughout overlapping
holomorphic disks centered on the real axis. -/
theorem eqOn_inter_real_centered_balls_of_analytic {f g : ℂ → F} {a b r s : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (a : ℂ) r))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (b : ℂ) s))
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ Metric.ball (a : ℂ) r ∩ Metric.ball (b : ℂ) s →
      f x = g x) :
    EqOn f g (Metric.ball (a : ℂ) r ∩ Metric.ball (b : ℂ) s) := by
  intro z hz
  have hre (c R : ℝ) (hc : z ∈ Metric.ball (c : ℂ) R) :
      (z.re : ℂ) ∈ Metric.ball (c : ℂ) R := by
    have h := Complex.abs_re_le_norm (z - (c : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    have hc' : ‖z - (c : ℂ)‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hc
    simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using h.trans_lt hc'
  have hx : (z.re : ℂ) ∈ Metric.ball (a : ℂ) r ∩ Metric.ball (b : ℂ) s :=
    ⟨hre a r hz.1, hre b s hz.2⟩
  have htend : Tendsto Complex.ofReal (𝓝[≠] z.re) (𝓝[≠] (z.re : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hxx
    exact Complex.ofReal_injective.ne hxx
  have hevent : ∀ᶠ x : ℝ in 𝓝 z.re, f (x : ℂ) = g (x : ℂ) := by
    have hmem := Complex.continuous_ofReal.continuousAt.preimage_mem_nhds
      ((Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds hx)
    filter_upwards [hmem] with x hx'
    exact hreal x hx'
  have hfreq : ∃ᶠ w in 𝓝[≠] (z.re : ℂ), f w = g w :=
    htend.frequently (hevent.filter_mono nhdsWithin_le_nhds).frequently
  exact (hf.mono inter_subset_left).eqOn_of_preconnected_of_frequently_eq
    (hg.mono inter_subset_right)
    ((convex_ball (a : ℂ) r).inter (convex_ball (b : ℂ) s)).isPreconnected hx hfreq hz

/-- The union of the quantitative extension disks about positive real times. -/
def positiveTimeNeighborhood (η : ℝ) : Set ℂ :=
  ⋃ t : {t : ℝ // 0 < t}, Metric.ball (t.val : ℂ) (η * min t.val 1)

theorem isOpen_positiveTimeNeighborhood (η : ℝ) : IsOpen (positiveTimeNeighborhood η) :=
  isOpen_iUnion fun _ ↦ Metric.isOpen_ball

theorem mem_positiveTimeNeighborhood_of_real {η t : ℝ} (hη : 0 < η) (ht : 0 < t) :
    (t : ℂ) ∈ positiveTimeNeighborhood η := by
  apply mem_iUnion.mpr
  exact ⟨⟨t, ht⟩, Metric.mem_ball_self (mul_pos hη (lt_min ht zero_lt_one))⟩

/-- The neighborhood contains a fixed-angle wedge near zero, continuing as a strip
about the positive real axis at large times. -/
theorem mem_positiveTimeNeighborhood_of_im_lt {η : ℝ} {z : ℂ}
    (hz : 0 < z.re) (him : |z.im| < η * min z.re 1) :
    z ∈ positiveTimeNeighborhood η := by
  apply mem_iUnion.mpr
  refine ⟨⟨z.re, hz⟩, ?_⟩
  have heq : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simpa only [Metric.mem_ball, dist_eq_norm, heq, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs] using him

/-- With the chosen small radii, the extension domain stays in the right half-plane. -/
theorem re_pos_of_mem_positiveTimeNeighborhood {η : ℝ} (hη : η ≤ 1)
    {z : ℂ} (hz : z ∈ positiveTimeNeighborhood η) : 0 < z.re := by
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  have hrad : η * min t.val 1 ≤ t.val := by
    calc
      _ ≤ 1 * min t.val 1 := mul_le_mul_of_nonneg_right hη (le_of_lt (lt_min t.property zero_lt_one))
      _ ≤ t.val := by simpa only [one_mul] using min_le_left t.val 1
  have hre := Complex.abs_re_le_norm (z - (t.val : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hn : ‖z - (t.val : ℂ)‖ < η * min t.val 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using ht
  have hlt := (abs_lt.mp (hre.trans_lt (hn.trans_le hrad))).1
  linarith

/-- Local holomorphic extensions with matching real restrictions glue to a single
holomorphic extension on the union of their disks. -/
theorem exists_analytic_extension_positiveTimeNeighborhood {f : ℝ → F} {η : ℝ}
    (hη : 0 < η)
    (hloc : ∀ t : ℝ, 0 < t → ∃ g : ℂ → F,
      AnalyticOnNhd ℂ g (Metric.ball (t : ℂ) (η * min t 1)) ∧
      ∀ s : ℝ, |s - t| < η * min t 1 → g s = f s) :
    ∃ g : ℂ → F, AnalyticOnNhd ℂ g (positiveTimeNeighborhood η) ∧
      (∀ t : ℝ, 0 < t → g t = f t) := by
  classical
  choose G hG hagree using fun t : {t : ℝ // 0 < t} ↦ hloc t.val t.property
  have hcover {z : ℂ} (hz : z ∈ positiveTimeNeighborhood η) :
      ∃ t : {t : ℝ // 0 < t}, z ∈ Metric.ball (t.val : ℂ) (η * min t.val 1) :=
    mem_iUnion.mp hz
  let g : ℂ → F := fun z ↦ if hz : z ∈ positiveTimeNeighborhood η then
    G (hcover hz).choose z else 0
  have heq (t : {t : ℝ // 0 < t}) {z : ℂ}
      (hz : z ∈ Metric.ball (t.val : ℂ) (η * min t.val 1)) : g z = G t z := by
    have hzU : z ∈ positiveTimeNeighborhood η := mem_iUnion.mpr ⟨t, hz⟩
    simp only [g, dif_pos hzU]
    apply eqOn_inter_real_centered_balls_of_analytic
      (hG ((hcover hzU).choose)) (hG t) _ ⟨(hcover hzU).choose_spec, hz⟩
    intro x hx
    have hx₁ : |x - ((hcover hzU).choose).val| < η * min ((hcover hzU).choose).val 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hx.1
    have hx₂ : |x - t.val| < η * min t.val 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hx.2
    exact (hagree _ x hx₁).trans (hagree t x hx₂).symm
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht⟩ := hcover hz
    apply (hG t z ht).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with w hw
    exact (heq t hw).symm
  · intro t ht
    have htball : (t : ℂ) ∈ Metric.ball (t : ℂ) (η * min t 1) :=
      Metric.mem_ball_self (mul_pos hη (lt_min ht zero_lt_one))
    rw [heq ⟨t, ht⟩ htball]
    exact hagree ⟨t, ht⟩ t (by simpa using mul_pos hη (lt_min ht zero_lt_one))

/-- A holomorphic extension to this domain is uniquely determined by its values at
positive real times. This makes the gluing independent of all local series choices. -/
theorem eqOn_positiveTimeNeighborhood_of_real {f g : ℂ → F} {η : ℝ} (hη : η ≤ 1)
    (hf : AnalyticOnNhd ℂ f (positiveTimeNeighborhood η))
    (hg : AnalyticOnNhd ℂ g (positiveTimeNeighborhood η))
    (hreal : ∀ t : ℝ, 0 < t → f t = g t) : EqOn f g (positiveTimeNeighborhood η) := by
  intro z hz
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  have hsub : Metric.ball (t.val : ℂ) (η * min t.val 1) ⊆ positiveTimeNeighborhood η :=
    fun w hw ↦ mem_iUnion.mpr ⟨t, hw⟩
  apply eqOn_inter_real_centered_balls_of_analytic (hf.mono hsub) (hg.mono hsub) _ ⟨ht, ht⟩
  intro s hs
  apply hreal
  simpa only [Complex.ofReal_re] using re_pos_of_mem_positiveTimeNeighborhood hη (hsub hs.1)

/-- A common norm bound on the local extensions survives gluing. -/
theorem exists_bounded_analytic_extension_positiveTimeNeighborhood
    {f : ℝ → F} {η M : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1)
    (hloc : ∀ t : ℝ, 0 < t → ∃ g : ℂ → F,
      AnalyticOnNhd ℂ g (Metric.ball (t : ℂ) (η * min t 1)) ∧
      (∀ s : ℝ, |s - t| < η * min t 1 → g s = f s) ∧
      ∀ z ∈ Metric.ball (t : ℂ) (η * min t 1), ‖g z‖ ≤ M) :
    ∃ g : ℂ → F, AnalyticOnNhd ℂ g (positiveTimeNeighborhood η) ∧
      (∀ t : ℝ, 0 < t → g t = f t) ∧
      ∀ z ∈ positiveTimeNeighborhood η, ‖g z‖ ≤ M := by
  obtain ⟨g, hg, heq⟩ := exists_analytic_extension_positiveTimeNeighborhood hη
    (fun t ht ↦ let ⟨G, hG, heq, _⟩ := hloc t ht; ⟨G, hG, heq⟩)
  refine ⟨g, hg, heq, ?_⟩
  intro z hz
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  obtain ⟨G, hG, hreal, hbound⟩ := hloc t.val t.property
  have hsub : Metric.ball (t.val : ℂ) (η * min t.val 1) ⊆ positiveTimeNeighborhood η :=
    fun w hw ↦ mem_iUnion.mpr ⟨t, hw⟩
  have heqG : g z = G z := by
    apply eqOn_inter_real_centered_balls_of_analytic (hg.mono hsub) hG _ ⟨ht, ht⟩
    intro s hs
    have hspos : 0 < s := by
      simpa only [Complex.ofReal_re] using re_pos_of_mem_positiveTimeNeighborhood hη₁ (hsub hs.1)
    have hsball : |s - t.val| < η * min t.val 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hs.2
    exact (heq s hspos).trans (hreal s hsball).symm
  rw [heqG]
  exact hbound z ht

/-- Translating to the right stays in the time-extension neighborhood. -/
theorem mem_positiveTimeNeighborhood_add_real {η : ℝ} (hη : 0 ≤ η)
    {z : ℂ} (hz : z ∈ positiveTimeNeighborhood η) {s : ℝ} (hs : 0 ≤ s) :
    z + (s : ℂ) ∈ positiveTimeNeighborhood η := by
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  apply mem_iUnion.mpr
  refine ⟨⟨t.val + s, add_pos_of_pos_of_nonneg t.property hs⟩, ?_⟩
  have hdist : dist (z + (s : ℂ)) ((t.val + s : ℝ) : ℂ) = dist z (t.val : ℂ) := by
    rw [Complex.ofReal_add, dist_add_right]
  rw [Metric.mem_ball, hdist]
  exact (Metric.mem_ball.mp ht).trans_le
    (mul_le_mul_of_nonneg_left (min_le_min (le_add_of_nonneg_right hs) le_rfl) hη)

end

end Planarwave
