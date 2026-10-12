/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator
public import Planarwave.Analysis.HolomorphicTimeExtension
public import Mathlib.Analysis.Analytic.Linear

@[expose] public section

/-!
# Real shifts of holomorphic semigroup extensions

The identity principle transfers the real semigroup law to complex time followed by
a nonnegative real time. Together with a bound near zero this gives strong continuity
at the vertex, without asserting operator-norm continuity there.
-/

open Filter Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A holomorphic time extension obeys the semigroup law for every nonnegative
real shift, including zero. -/
theorem holomorphicExtension_add_real (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) {g : ℂ → (E →L[ℂ] E)}
    (hg : AnalyticOnNhd ℂ g (Planarwave.positiveTimeNeighborhood η))
    (hreal : ∀ t : ℝ, 0 < t → g t = S t.toNNReal)
    {z : ℂ} (hz : z ∈ Planarwave.positiveTimeNeighborhood η)
    {s : ℝ} (hs : 0 ≤ s) : g (z + (s : ℂ)) = (g z).comp (S s.toNNReal) := by
  have hshift : AnalyticOnNhd ℂ (fun w : ℂ ↦ g (w + (s : ℂ)))
      (Planarwave.positiveTimeNeighborhood η) := by
    intro w hw
    exact (hg _ (Planarwave.mem_positiveTimeNeighborhood_add_real hη.le hw hs)).comp
      (f := fun w : ℂ ↦ w + (s : ℂ)) (analyticAt_id.add analyticAt_const)
  have hcomp : AnalyticOnNhd ℂ (fun w ↦ (g w).comp (S s.toNNReal))
      (Planarwave.positiveTimeNeighborhood η) := by
    intro w hw
    exact (((ContinuousLinearMap.compL ℂ E E E).flip (S s.toNNReal)).analyticAt (g w)).comp (hg w hw)
  apply Planarwave.eqOn_positiveTimeNeighborhood_of_real hη₁ hshift hcomp _ hz
  intro t ht
  rw [← Complex.ofReal_add, hreal _ (add_pos_of_pos_of_nonneg ht hs), hreal _ ht,
    Real.toNNReal_add ht.le hs, S.map_add]

/-- The complex semigroup law holds on a fixed-angle wedge near the time origin.
The restriction on the sum of real parts keeps both times and their sum inside
the local holomorphic extension domain. -/
theorem holomorphicExtension_add_small (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) {g : ℂ → (E →L[ℂ] E)}
    (hg : AnalyticOnNhd ℂ g (Planarwave.positiveTimeNeighborhood η))
    (hreal : ∀ t : ℝ, 0 < t → g t = S t.toNNReal)
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re)
    (hzi : |z.im| < η * z.re) (hwi : |w.im| < η * w.re)
    (hzw : z.re + w.re ≤ 1) : g (z + w) = (g z).comp (g w) := by
  have hz₁ : z.re ≤ 1 := by linarith
  have hw₁ : w.re ≤ 1 := by linarith
  have hzU : z ∈ Planarwave.positiveTimeNeighborhood η :=
    Planarwave.mem_positiveTimeNeighborhood_of_im_lt hz (by rwa [min_eq_left hz₁])
  have hsub : Metric.ball (w.re : ℂ) (η * w.re) ⊆ Planarwave.positiveTimeNeighborhood η := by
    intro v hv
    exact mem_iUnion.mpr ⟨⟨w.re, hw⟩, by simpa only [min_eq_left hw₁] using hv⟩
  have hdist (v : ℂ) : dist v (v.re : ℂ) = |v.im| := by
    have heq : v - (v.re : ℂ) = (v.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    simp only [dist_eq_norm, heq, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∀ v ∈ Metric.ball (w.re : ℂ) (η * w.re),
      z + v ∈ Planarwave.positiveTimeNeighborhood η := by
    intro v hv
    apply mem_iUnion.mpr
    refine ⟨⟨z.re + w.re, add_pos hz hw⟩, ?_⟩
    rw [Metric.mem_ball, min_eq_left hzw, Complex.ofReal_add]
    calc
      dist (z + v) ((z.re : ℂ) + (w.re : ℂ)) ≤
          dist z (z.re : ℂ) + dist v (w.re : ℂ) := dist_add_add_le _ _ _ _
      _ < η * z.re + η * w.re := add_lt_add (by rwa [hdist]) (Metric.mem_ball.mp hv)
      _ = η * (z.re + w.re) := by ring
  have hshift : AnalyticOnNhd ℂ (fun v ↦ g (z + v)) (Metric.ball (w.re : ℂ) (η * w.re)) := by
    intro v hv
    exact (hg _ (hsum v hv)).comp (f := fun v ↦ z + v) (analyticAt_const.add analyticAt_id)
  have hcomp : AnalyticOnNhd ℂ (fun v ↦ (g z).comp (g v))
      (Metric.ball (w.re : ℂ) (η * w.re)) := by
    intro v hv
    exact ((ContinuousLinearMap.compL ℂ E E E (g z)).analyticAt (g v)).comp (hg v (hsub hv))
  have hwball : w ∈ Metric.ball (w.re : ℂ) (η * w.re) := by
    rwa [Metric.mem_ball, hdist]
  apply Planarwave.eqOn_inter_real_centered_balls_of_analytic hshift hcomp _ ⟨hwball, hwball⟩
  intro s hs
  have hspos : 0 < s := by
    simpa only [Complex.ofReal_re] using
      Planarwave.re_pos_of_mem_positiveTimeNeighborhood hη₁ (hsub hs.1)
  rw [S.holomorphicExtension_add_real hη hη₁ hg hreal hzU hspos.le, hreal s hspos]

/-- Boundedness of the complex extension and the real-shift law imply strong
continuity at zero through the entire extension neighborhood. -/
theorem tendsto_holomorphicExtension_zero (S : C0Semigroup ℂ E)
    {η M : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) (hM : 0 ≤ M)
    {g : ℂ → (E →L[ℂ] E)}
    (hg : AnalyticOnNhd ℂ g (Planarwave.positiveTimeNeighborhood η))
    (hreal : ∀ t : ℝ, 0 < t → g t = S t.toNNReal)
    (hbound : ∀ z ∈ Planarwave.positiveTimeNeighborhood η, ‖g z‖ ≤ M) (x : E) :
    Tendsto (fun z ↦ g z x) (𝓝[Planarwave.positiveTimeNeighborhood η] 0) (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have htol : 0 < ε / (2 * (M + 1)) := by positivity
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp
    (S.continuous_realOrbit x).continuousAt (ε / (2 * (M + 1))) htol
  let s : ℝ := δ / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have happ : ‖S s.toNNReal x - x‖ < ε / (2 * (M + 1)) := by
    have hd : dist s (0 : ℝ) < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs]
      dsimp [s]
      linarith
    simpa only [realOrbit, Real.toNNReal_zero, S.zero_apply, dist_eq_norm] using hδbound hd
  have hc : ContinuousAt (fun z : ℂ ↦ g (z + (s : ℂ)) x) 0 := by
    have hgs := (hg _ (Planarwave.mem_positiveTimeNeighborhood_of_real hη hs)).continuousAt
    have hcadd : ContinuousAt (fun z : ℂ ↦ z + (s : ℂ)) 0 := continuousAt_id.add continuousAt_const
    have hcomp : ContinuousAt (fun z : ℂ ↦ g (z + (s : ℂ))) 0 := by
      have hgs' : ContinuousAt g (0 + (s : ℂ)) := by simpa only [zero_add] using hgs
      exact hgs'.comp (f := fun z : ℂ ↦ z + (s : ℂ)) hcadd
    exact hcomp.clm_apply continuousAt_const
  have hshiftlim : ∀ᶠ z : ℂ in 𝓝 0,
      ‖g (z + (s : ℂ)) x - S s.toNNReal x‖ < ε / 2 := by
    have h := hc.tendsto.eventually (Metric.ball_mem_nhds (g (0 + (s : ℂ)) x)
      (show 0 < ε / 2 by positivity))
    simpa only [Metric.mem_ball, dist_eq_norm, zero_add, hreal s hs] using h
  filter_upwards [hshiftlim.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzU
  rw [dist_eq_norm]
  have hdecomp : g z x - x = g z (x - S s.toNNReal x) +
      (g (z + (s : ℂ)) x - S s.toNNReal x) + (S s.toNNReal x - x) := by
    rw [S.holomorphicExtension_add_real hη hη₁ hg hreal hzU hs.le,
      ContinuousLinearMap.comp_apply, _root_.map_sub]
    abel
  have hgapp : ‖g z (x - S s.toNNReal x)‖ ≤ M * ‖S s.toNNReal x - x‖ := by
    calc
      _ ≤ ‖g z‖ * ‖x - S s.toNNReal x‖ := (g z).le_opNorm _
      _ ≤ M * ‖S s.toNNReal x - x‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right (hbound z hzU) (norm_nonneg _)
  have hsmall : (M + 1) * ‖S s.toNNReal x - x‖ < ε / 2 := by
    have h := (lt_div_iff₀ (show 0 < 2 * (M + 1) by positivity)).mp happ
    nlinarith
  rw [hdecomp]
  exact (norm_add_le _ _).trans_lt (by
    have htriangle := norm_add_le (g z (x - S s.toNNReal x))
      (g (z + (s : ℂ)) x - S s.toNNReal x)
    linarith)

end

end C0Semigroup
