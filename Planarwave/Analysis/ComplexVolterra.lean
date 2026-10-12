/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HolomorphicIntegral
public import Planarwave.Analysis.ComplexTimeSector
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

/-!
# The complex-time Volterra operator

Integration over the open unit interval avoids imposing operator-norm continuity at
time zero. The endpoints are null sets. The rescaled convolution is holomorphic and
gains one power of time and the factor `1/(n+1)` in its norm bound.
-/

open Filter MeasureTheory Metric Set Topology

namespace Planarwave

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def complexVolterraKernel (G : ℂ → (E →L[ℂ] E)) (B : E →L[ℂ] E)
    (H : ℂ → (E →L[ℂ] E)) (z : ℂ) (r : ℝ) : E →L[ℂ] E :=
  (G (((1 - r : ℝ) : ℂ) * z)).comp (B.comp (H ((r : ℂ) * z)))

def complexVolterra (G : ℂ → (E →L[ℂ] E)) (B : E →L[ℂ] E)
    (H : ℂ → (E →L[ℂ] E)) (z : ℂ) : E →L[ℂ] E :=
  z • ∫ r in Ioo (0 : ℝ) 1, complexVolterraKernel G B H z r

omit [CompleteSpace E] in
theorem norm_complexVolterraKernel_le
    {η M C ω : ℝ} (hM : 0 ≤ M) (_hC : 0 ≤ C)
    {G H : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E) (n : ℕ)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hH : ∀ z ∈ complexTimeSector η, ‖H z‖ ≤ C * Real.exp (ω * ‖z‖) * ‖z‖ ^ n)
    {z : ℂ} (hz : z ∈ complexTimeSector η) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖complexVolterraKernel G B H z r‖ ≤
      M * C * ‖B‖ * Real.exp (ω * ‖z‖) * ‖z‖ ^ n * r ^ n := by
  have hnorm (s : ℝ) (hs : 0 ≤ s) : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hG' := hG _ (real_mul_mem_complexTimeSector hz (sub_pos.mpr hr.2))
  have hH' := hH _ (real_mul_mem_complexTimeSector hz hr.1)
  rw [hnorm (1 - r) (sub_nonneg.mpr hr.2.le)] at hG'
  rw [hnorm r hr.1.le] at hH'
  have hexp : Real.exp (ω * ((1 - r) * ‖z‖)) * Real.exp (ω * (r * ‖z‖)) =
      Real.exp (ω * ‖z‖) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ ‖G (((1 - r : ℝ) : ℂ) * z)‖ * (‖B‖ * ‖H ((r : ℂ) * z)‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (M * Real.exp (ω * ((1 - r) * ‖z‖))) *
        (‖B‖ * (C * Real.exp (ω * (r * ‖z‖)) * (r * ‖z‖) ^ n)) :=
      mul_le_mul hG' (mul_le_mul_of_nonneg_left hH' (norm_nonneg _)) (by positivity) (by positivity)
    _ = (M * C * ‖B‖ * ‖z‖ ^ n * r ^ n) *
        (Real.exp (ω * ((1 - r) * ‖z‖)) * Real.exp (ω * (r * ‖z‖))) := by rw [mul_pow]; ring
    _ = _ := by rw [hexp]; ring

omit [CompleteSpace E] in
/-- Each convolution gains a power of time and divides by the new exponent. -/
theorem norm_complexVolterra_le
    {η M C ω : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    {G H : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E) (n : ℕ)
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hH : ∀ z ∈ complexTimeSector η, ‖H z‖ ≤ C * Real.exp (ω * ‖z‖) * ‖z‖ ^ n)
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    ‖complexVolterra G B H z‖ ≤
      (M * C * ‖B‖ / (n + 1)) * Real.exp (ω * ‖z‖) * ‖z‖ ^ (n + 1) := by
  let K := M * C * ‖B‖ * Real.exp (ω * ‖z‖) * ‖z‖ ^ n
  have hint : IntegrableOn (fun r : ℝ ↦ K * r ^ n) (Ioo 0 1) :=
    ((by fun_prop : Continuous (fun r : ℝ ↦ K * r ^ n)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hb : ‖∫ r in Ioo (0 : ℝ) 1, complexVolterraKernel G B H z r‖ ≤
      ∫ r in Ioo (0 : ℝ) 1, K * r ^ n := by
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact norm_complexVolterraKernel_le hM hC B n hG hH hz hr
  have heval : (∫ r in Ioo (0 : ℝ) 1, K * r ^ n) = K / (n + 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, mul_one_div]
  rw [heval] at hb
  calc
    ‖complexVolterra G B H z‖ = ‖z‖ * ‖∫ r in Ioo (0 : ℝ) 1,
        complexVolterraKernel G B H z r‖ := norm_smul _ _
    _ ≤ ‖z‖ * (K / (n + 1)) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by dsimp [K]; rw [pow_succ]; ring

omit [CompleteSpace E] in
theorem continuousOn_complexVolterraKernel
    {η : ℝ} {G H : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hH : AnalyticOnNhd ℂ H (complexTimeSector η))
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    ContinuousOn (complexVolterraKernel G B H z) (Ioo 0 1) := by
  have hleft : ContinuousOn (fun r : ℝ ↦ G (((1 - r : ℝ) : ℂ) * z)) (Ioo 0 1) :=
    hG.continuousOn.comp (by fun_prop) (fun r hr ↦ real_mul_mem_complexTimeSector hz (sub_pos.mpr hr.2))
  have hright : ContinuousOn (fun r : ℝ ↦ H ((r : ℂ) * z)) (Ioo 0 1) :=
    hH.continuousOn.comp (by fun_prop) (fun r hr ↦ real_mul_mem_complexTimeSector hz hr.1)
  exact hleft.clm_comp (continuousOn_const.clm_comp hright)

omit [CompleteSpace E] in
theorem analyticOnNhd_complexVolterraKernel
    {η : ℝ} {G H : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E)
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hH : AnalyticOnNhd ℂ H (complexTimeSector η))
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (fun z ↦ complexVolterraKernel G B H z r) (complexTimeSector η) := by
  intro z hz
  have hleft := (hG _ (real_mul_mem_complexTimeSector hz (sub_pos.mpr hr.2))).comp
    (f := fun z : ℂ ↦ ((1 - r : ℝ) : ℂ) * z) (analyticAt_const.mul analyticAt_id)
  have hright := (hH _ (real_mul_mem_complexTimeSector hz hr.1)).comp
    (f := fun z : ℂ ↦ (r : ℂ) * z) (analyticAt_const.mul analyticAt_id)
  have hright' := ((ContinuousLinearMap.compL ℂ E E E B).analyticAt (H ((r : ℂ) * z))).comp
    (f := fun z : ℂ ↦ H ((r : ℂ) * z)) hright
  exact ((ContinuousLinearMap.compL ℂ E E E).analyticAt_bilinear _).comp (hleft.prod hright')

/-- The rescaled Volterra convolution preserves holomorphy on the sector. -/
theorem analyticOnNhd_complexVolterra
    {η M C ω : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hω : 0 ≤ ω)
    {G H : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E) (n : ℕ)
    (hGa : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hHa : AnalyticOnNhd ℂ H (complexTimeSector η))
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hH : ∀ z ∈ complexTimeSector η, ‖H z‖ ≤ C * Real.exp (ω * ‖z‖) * ‖z‖ ^ n) :
    AnalyticOnNhd ℂ (complexVolterra G B H) (complexTimeSector η) := by
  have hi : AnalyticOnNhd ℂ (fun z ↦ ∫ r in Ioo (0 : ℝ) 1, complexVolterraKernel G B H z r)
      (complexTimeSector η) := by
    apply analyticOnNhd_integral_of_locally_bounded (isOpen_complexTimeSector η)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact analyticOnNhd_complexVolterraKernel B hGa hHa hr
    · intro z hz
      exact (continuousOn_complexVolterraKernel B hGa hHa hz).aestronglyMeasurable measurableSet_Ioo
    · intro z hz
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (isOpen_complexTimeSector η) z hz
      refine ⟨δ / 2, by positivity, by simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hsub,
        M * C * ‖B‖ * Real.exp (ω * (‖z‖ + δ)) * (‖z‖ + δ) ^ n, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr w hw
      have hw' : w ∈ ball z δ := by simpa only [show 2 * (δ / 2) = δ by ring] using hw
      have hnw : ‖w‖ ≤ ‖z‖ + δ := by
        have h : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        have hd : ‖w - z‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hw'
        linarith
      have hr₀ : 0 ≤ r := hr.1.le
      calc
        _ ≤ M * C * ‖B‖ * Real.exp (ω * ‖w‖) * ‖w‖ ^ n * r ^ n :=
          norm_complexVolterraKernel_le hM hC B n hG hH (hsub hw') hr
        _ ≤ M * C * ‖B‖ * Real.exp (ω * (‖z‖ + δ)) * (‖z‖ + δ) ^ n * 1 := by
          apply mul_le_mul _ (pow_le_one₀ hr.1.le hr.2.le) (by positivity) (by positivity)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnw hω)) (by positivity))
            (pow_le_pow_left₀ (norm_nonneg _) hnw n) (by positivity) (by positivity)
        _ = _ := mul_one _
  intro z hz
  exact analyticAt_id.smul (hi z hz)

omit [CompleteSpace E] in
/-- The operator-valued kernel is Bochner integrable, despite possible failure of
operator-norm continuity at the endpoints. -/
theorem integrableOn_complexVolterraKernel
    {η M C ω : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    {G H : ℂ → (E →L[ℂ] E)} (B : E →L[ℂ] E) (n : ℕ)
    (hGa : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hHa : AnalyticOnNhd ℂ H (complexTimeSector η))
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hH : ∀ z ∈ complexTimeSector η, ‖H z‖ ≤ C * Real.exp (ω * ‖z‖) * ‖z‖ ^ n)
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    IntegrableOn (complexVolterraKernel G B H z) (Ioo 0 1) := by
  apply Integrable.of_bound
    ((continuousOn_complexVolterraKernel B hGa hHa hz).aestronglyMeasurable measurableSet_Ioo)
    (M * C * ‖B‖ * Real.exp (ω * ‖z‖) * ‖z‖ ^ n)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact (norm_complexVolterraKernel_le hM hC B n hG hH hz hr).trans
    (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hr.1.le hr.2.le))

end

end Planarwave
