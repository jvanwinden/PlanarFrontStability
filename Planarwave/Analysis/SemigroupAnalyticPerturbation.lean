/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ComplexDysonSeries
public import Planarwave.Analysis.SemigroupPerturbationBound
public import Planarwave.Analysis.SemigroupSector

@[expose] public section

/-!
# Analyticity of the bounded-perturbation semigroup

The complex Dyson series agrees term by term on positive real times with the Volterra
series used to construct `boundedPerturbation`. Thus the holomorphic extension belongs
to the actual perturbed semigroup, rather than an independently postulated evolution.
-/

open Filter MeasureTheory Set Topology Planarwave

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Each complex Dyson term restricts to the corresponding real Volterra iterate
on every finite time interval. The null endpoints require no norm limit at zero. -/
theorem complexDysonTerm_real_apply (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {η M ω : ℝ} (hη : 0 < η) (hM : 0 ≤ M) (hω : 0 ≤ ω)
    {G : ℂ → (E →L[ℂ] E)} (hGa : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    (T : NNReal) (x : E) (n : ℕ) (t : Icc (0 : ℝ) (T : ℝ)) (ht : 0 < (t : ℝ)) :
    complexDysonTerm G B n (t : ℝ) x =
      ((S.perturbationOperator B T) ^ n) (S.freePath T x) t := by
  induction n generalizing t with
  | zero =>
    change G (t : ℝ) x = S (t : ℝ).toNNReal x
    rw [hreal _ ht]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, perturbationOperator_apply]
    let v := ((S.perturbationOperator B T) ^ n) (S.freePath T x)
    change complexVolterra G B (complexDysonTerm G B n) (t : ℝ) x =
      S.duhamel (fun s ↦ B (extendTimePath v s)) t
    have hint := integrableOn_complexVolterraKernel hM
      (C := M * (M * ‖B‖) ^ n / n.factorial) (by positivity) B n hGa
      (analyticOnNhd_complexDysonTerm hM hω B hGa hG n) hG
      (fun _ hz ↦ norm_complexDysonTerm_le hM B hG n hz) (mem_complexTimeSector_real hη ht)
    have hscale : (t : ℝ) • (∫ r in (0 : ℝ)..1,
        S.realOrbit (B (extendTimePath v ((t : ℝ) * r))) ((t : ℝ) - (t : ℝ) * r)) =
        S.duhamel (fun s ↦ B (extendTimePath v s)) t := by
      simpa only [duhamel, mul_zero, mul_one] using!
        intervalIntegral.smul_integral_comp_mul_left
          (fun s ↦ S.realOrbit (B (extendTimePath v s)) ((t : ℝ) - s)) (t : ℝ) (a := 0) (b := 1)
    have hcoe (a : ℝ) (v : E) : (a : ℂ) • v = a • v := by
      simpa only using! (RCLike.real_smul_eq_coe_smul (K := ℂ) a v).symm
    rw [complexVolterra, smul_apply, ContinuousLinearMap.integral_apply hint]
    rw [hcoe, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, ← hscale]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro r hr
    have htr : (t : ℝ) * r ∈ Icc (0 : ℝ) (T : ℝ) :=
      ⟨mul_nonneg ht.le hr.1.le, (mul_le_of_le_one_right ht.le hr.2.le).trans t.2.2⟩
    have hc₁ : ((1 - r : ℝ) : ℂ) * (t : ℝ) = (((t : ℝ) - (t : ℝ) * r : ℝ) : ℂ) := by
      push_cast
      ring
    have hc₂ : (r : ℂ) * (t : ℝ) = (((t : ℝ) * r : ℝ) : ℂ) := by push_cast; ring
    have hleft : 0 < (t : ℝ) - (t : ℝ) * r := by nlinarith [hr.2]
    dsimp only [complexVolterraKernel]
    rw [hc₁, hc₂, hreal _ hleft, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ih ⟨(t : ℝ) * r, htr⟩ (mul_pos ht hr.1)]
    rw [show extendTimePath v ((t : ℝ) * r) = v ⟨(t : ℝ) * r, htr⟩ from
      extendTimePath_coe v ⟨(t : ℝ) * r, htr⟩]
    rfl

/-- Identification with the already constructed real-time bounded perturbation. -/
theorem complexDysonSum_real (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {η M ω : ℝ} (hη : 0 < η) (hM : 0 ≤ M) (hω : 0 ≤ ω)
    {G : ℂ → (E →L[ℂ] E)} (hGa : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    {t : ℝ} (ht : 0 < t) :
    complexDysonSum G B t = S.boundedPerturbation B t.toNNReal := by
  apply ContinuousLinearMap.ext
  intro x
  have hs := summable_complexDysonTerm hM B hG (mem_complexTimeSector_real hη ht)
  have heval := (ContinuousLinearMap.apply ℂ E x).map_tsum hs
  have heval' : (∑' n, complexDysonTerm G B n (t : ℂ)) x =
      ∑' n, complexDysonTerm G B n (t : ℂ) x := by
    simpa only [ContinuousLinearMap.apply_apply] using! heval
  change (∑' n, complexDysonTerm G B n (t : ℂ)) x = S.perturbedOperator B t.toNNReal x
  rw [heval', S.perturbedOperator_eq_tsum]
  apply tsum_congr
  intro n
  simpa only [Real.coe_toNNReal _ ht.le] using!
    S.complexDysonTerm_real_apply B hη hM hω hGa hG hreal t.toNNReal x n
      ⟨t, ht.le, by simp only [Real.coe_toNNReal _ ht.le]; rfl⟩ ht

/-- Bounded perturbation preserves analytic generation on the same complex time
sector. The bound and strong continuity belong to the already constructed
`boundedPerturbation`, identified through its real Volterra series. -/
theorem exists_boundedPerturbation_holomorphic_sector (S : C0Semigroup ℂ E) (B : E →L[ℂ] E)
    {η M ω : ℝ} (hη : 0 < η) (hM : 0 ≤ M) (hω : 0 ≤ ω)
    {G : ℂ → (E →L[ℂ] E)} (hGa : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hG : ∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * ‖z‖))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    (hzero : ∀ x, Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x)) :
    ∃ H : ℂ → (E →L[ℂ] E), AnalyticOnNhd ℂ H (complexTimeSector η) ∧
      (∀ t : ℝ, 0 < t → H t = S.boundedPerturbation B t.toNNReal) ∧
      (∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
        H (z + w) = (H z).comp (H w)) ∧
      (∀ x, Tendsto (fun z ↦ H z x) (𝓝[complexTimeSector η] 0) (𝓝 x)) ∧
      (∀ z ∈ complexTimeSector η, ‖H z‖ ≤ M * Real.exp ((ω + M * ‖B‖) * ‖z‖)) := by
  have ha := analyticOnNhd_complexDysonSum hM hω B hGa hG
  have heq : ∀ t : ℝ, 0 < t → complexDysonSum G B t = S.boundedPerturbation B t.toNNReal :=
    fun _ ht ↦ S.complexDysonSum_real B hη hM hω hGa hG hreal ht
  exact ⟨complexDysonSum G B, ha, heq,
    fun _ hz _ hw ↦ (S.boundedPerturbation B).holomorphicSectorExtension_add hη ha heq hz hw,
    tendsto_complexDysonSum_zero hM B hG hzero,
    fun _ hz ↦ norm_complexDysonSum_le hM B hG hz⟩

end

end C0Semigroup
