/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ForcedColeHopfBounds
public import Planarwave.Analysis.ColeHopfEvolution
public import Planarwave.Analysis.ColeHopfPDE

@[expose] public section

/-!
# Inverting the small forced Cole--Hopf variable

The second part of the a priori argument in Lemma `lem:xiAP` uses
`|β ξ| ≤ 1/2`. We prove the inverse's uniform Lipschitz bound on this
range, construct its BUC representative, and verify the forced PDE
cancellation. The constants and smallness threshold are chosen before
the solution, the forcing, and the final time.
-/

open Set
open scoped ContDiff Gradient Laplacian

namespace Planarwave

noncomputable section

/-- The small range used in the paper lies strictly inside the logarithm's
domain, for either sign of `β` and also for `β = 0`. -/
theorem mem_coleHopfDomain_of_abs_mul_le_half {β x : ℝ} (hx : |β * x| ≤ 1 / 2) :
    x ∈ coleHopfDomain β := by
  rw [mem_coleHopfDomain]
  have := (abs_le.mp hx).1
  linarith

theorem Icc_subset_coleHopfDomain_of_small_radius {β R : ℝ}
    (hsmall : |β| * R ≤ 1 / 2) : Icc (-R) R ⊆ coleHopfDomain β := by
  intro x hx
  apply mem_coleHopfDomain_of_abs_mul_le_half
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (abs_le.mpr hx) (abs_nonneg β)).trans hsmall

/-- The inverse's derivative is at most two throughout the small range. -/
theorem lipschitzOnWith_coleHopfInv_Icc {β R : ℝ}
    (hsmall : |β| * R ≤ 1 / 2) :
    LipschitzOnWith 2 (coleHopfInv β) (Icc (-R) R) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact (hasDerivAt_coleHopfInv (Icc_subset_coleHopfDomain_of_small_radius hsmall hx)).differentiableAt
  · intro x hx
    have habs : |β * x| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr hx) (abs_nonneg β)).trans hsmall
    have hhalf : (1 : ℝ) / 2 ≤ 1 + β * x := by linarith [(abs_le.mp habs).1]
    have hpos : 0 < 1 + β * x := by linarith
    rw [deriv_coleHopfInv (mem_coleHopfDomain_of_abs_mul_le_half habs)]
    apply NNReal.coe_le_coe.mp
    change ‖(1 + β * x)⁻¹‖ ≤ (2 : ℝ)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hpos).mpr (by linarith)
  · exact convex_Icc _ _

/-- Zero-order bound for the logarithmic inverse, uniformly in `β`. -/
theorem abs_coleHopfInv_le_two_mul_abs {β x : ℝ} (hx : |β * x| ≤ 1 / 2) :
    |coleHopfInv β x| ≤ 2 * |x| := by
  have h := lipschitzOnWith_coleHopfInv_Icc (R := |x|) (β := β) (by rwa [← abs_mul])
  have hxmem : x ∈ Icc (-|x|) |x| := abs_le.mp (le_refl _)
  have hzero : (0 : ℝ) ∈ Icc (-|x|) |x| := ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩
  simpa [Real.dist_eq] using h.dist_le_mul x hxmem 0 hzero

section BUCInverse

variable {E : Type*} [UniformSpace E]

/-- The inverse transform on a BUC field satisfying the small-range bound. -/
def coleHopfInvSmallBUC (β : ℝ) (ξ : BUC E ℝ) (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) : BUC E ℝ :=
  ξ.compOnIcc (coleHopfInv β)
    ((contDiffOn_coleHopfInv β).continuousOn.mono
      (Icc_subset_coleHopfDomain_of_small_radius hsmall))
    (fun x ↦ abs_le.mp (ξ.norm_apply_le x))

@[simp]
theorem coleHopfInvSmallBUC_apply (β : ℝ) (ξ : BUC E ℝ) (hsmall : |β| * ‖ξ‖ ≤ 1 / 2)
    (x : E) : coleHopfInvSmallBUC β ξ hsmall x = coleHopfInv β (ξ x) := rfl

theorem norm_coleHopfInvSmallBUC_le (β : ℝ) (ξ : BUC E ℝ) (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) :
    ‖coleHopfInvSmallBUC β ξ hsmall‖ ≤ 2 * ‖ξ‖ := by
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  have hx : |β * ξ x| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (ξ.norm_apply_le x) (abs_nonneg β)).trans hsmall
  exact (abs_coleHopfInv_le_two_mul_abs hx).trans
    (mul_le_mul_of_nonneg_left (ξ.norm_apply_le x) (by norm_num))

theorem coleHopfBUC_coleHopfInvSmallBUC (β : ℝ) (ξ : BUC E ℝ)
    (hsmall : |β| * ‖ξ‖ ≤ 1 / 2) :
    coleHopfBUC β (coleHopfInvSmallBUC β ξ hsmall) = ξ := by
  ext x
  exact coleHopf_coleHopfInv (Icc_subset_coleHopfDomain_of_small_radius hsmall
    (abs_le.mp (ξ.norm_apply_le x)))

/-- The inverse is two-Lipschitz in the BUC norm on the small range. -/
theorem norm_coleHopfInvSmallBUC_sub_le (β : ℝ) (ξ η : BUC E ℝ)
    (hξ : |β| * ‖ξ‖ ≤ 1 / 2) (hη : |β| * ‖η‖ ≤ 1 / 2) :
    ‖coleHopfInvSmallBUC β ξ hξ - coleHopfInvSmallBUC β η hη‖ ≤ 2 * ‖ξ - η‖ := by
  have hmax : |β| * max ‖ξ‖ ‖η‖ ≤ 1 / 2 := by
    rw [mul_max_of_nonneg _ _ (abs_nonneg β)]
    exact max_le hξ hη
  have hLip := lipschitzOnWith_coleHopfInv_Icc hmax
  apply (BUC.norm_le (by positivity)).mpr
  intro x
  have hx : ξ x ∈ Icc (-max ‖ξ‖ ‖η‖) (max ‖ξ‖ ‖η‖) :=
    abs_le.mp ((ξ.norm_apply_le x).trans (le_max_left _ _))
  have hy : η x ∈ Icc (-max ‖ξ‖ ‖η‖) (max ‖ξ‖ ‖η‖) :=
    abs_le.mp ((η.norm_apply_le x).trans (le_max_right _ _))
  have hp : |coleHopfInv β (ξ x) - coleHopfInv β (η x)| ≤ 2 * |ξ x - η x| := by
    simpa [Real.dist_eq] using hLip.dist_le_mul (ξ x) hx (η x) hy
  exact hp.trans (mul_le_mul_of_nonneg_left ((ξ - η).norm_apply_le x) (by norm_num))

/-- Smallness on a time interval produces an actual BUC-valued phase path,
continuous up to both endpoints. Values outside the interval are immaterial. -/
theorem exists_continuous_coleHopfInv_on {β T : ℝ} (ξ : ℝ → BUC E ℝ)
    (hξ : ContinuousOn ξ (Icc 0 T)) (hsmall : ∀ t ∈ Icc 0 T, |β| * ‖ξ t‖ ≤ 1 / 2) :
    ∃ σ : ℝ → BUC E ℝ, ContinuousOn σ (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T,
        (∀ x, σ t x = coleHopfInv β (ξ t x)) ∧
        coleHopfBUC β (σ t) = ξ t ∧ ‖σ t‖ ≤ 2 * ‖ξ t‖ := by
  classical
  let σ := fun t ↦ if ht : t ∈ Icc 0 T then coleHopfInvSmallBUC β (ξ t) (hsmall t ht) else 0
  have heq : ∀ t (ht : t ∈ Icc 0 T), σ t = coleHopfInvSmallBUC β (ξ t) (hsmall t ht) := by
    intro t ht
    simp only [σ, dif_pos ht]
  refine ⟨σ, ?_, ?_⟩
  · intro t ht
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp (hξ t ht) (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
    have hdiff := norm_coleHopfInvSmallBUC_sub_le β (ξ s) (ξ t) (hsmall s hs) (hsmall t ht)
    rw [← heq s hs, ← heq t ht] at hdiff
    have hnear := hcont hs hst
    rw [dist_eq_norm] at hnear ⊢
    linarith
  · intro t ht
    rw [heq t ht]
    exact ⟨fun _ ↦ rfl, coleHopfBUC_coleHopfInvSmallBUC β (ξ t) (hsmall t ht),
      norm_coleHopfInvSmallBUC_le β (ξ t) (hsmall t ht)⟩

end BUCInverse

section APriori

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The zero-order a priori part of Lemma `lem:xiAP`, with constants chosen
uniformly before `T`, `M`, and the forcing. This does not assert existence. -/
theorem exists_forcedColeHopf_small_bound (β C : ℝ) (hC : 0 < C) :
    ∃ C₀ > 0, ∃ M₀ > 0, ∀ (a T M : ℝ) (g ξ : ℝ → BUC E ℝ),
      0 ≤ T → 0 ≤ M → M ≤ M₀ → ContinuousOn g (Icc 0 T) →
      (∀ t ∈ Icc 0 T, ‖g t‖ ≤ C * M * (1 + t) ^ (-(5 : ℝ) / 4)) →
      IsForcedColeHopfMild a β g ξ T →
      ∀ t ∈ Icc 0 T, ‖ξ t‖ ≤ C₀ * M ∧ |β| * ‖ξ t‖ ≤ 1 / 2 := by
  let C₀ := 4 * C * Real.exp (4 * |β| * C)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let M₀ := min 1 (1 / (2 * (|β| * C₀ + 1)))
  have hden : 0 < 2 * (|β| * C₀ + 1) := by positivity
  have hM₀ : 0 < M₀ := lt_min (by norm_num) (div_pos (by norm_num) hden)
  refine ⟨C₀, hC₀, M₀, hM₀, ?_⟩
  intro a T M g ξ hT hM hMM hg hdecay hξ t ht
  have hM1 : M ≤ 1 := hMM.trans (min_le_left _ _)
  have hbound := hξ.norm_le_of_decay hg hT hC.le hM hM1 hdecay ht
  refine ⟨hbound, ?_⟩
  have hMs : M * (2 * (|β| * C₀ + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (hMM.trans (min_le_right _ _))
  have hprod : |β| * ‖ξ t‖ ≤ |β| * (C₀ * M) :=
    mul_le_mul_of_nonneg_left hbound (abs_nonneg β)
  nlinarith

end APriori

section PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Inverting a classical solution of the forced Cole--Hopf equation gives
the forced viscous Hamilton--Jacobi equation, with the same forcing `g`. -/
theorem hasDerivAt_coleHopfInv_of_forced_heat
    (ξ : ℝ → E → ℝ) (t : ℝ) (x : E) (a c β g : ℝ)
    (htime : HasDerivAt (fun s ↦ ξ s x)
      (a * Δ (ξ t) x - (1 + β * ξ t x) * g) t)
    (hspace : ContDiff ℝ 2 (ξ t))
    (hdomain : ∀ y, ξ t y ∈ coleHopfDomain β)
    (hcancel : a * β = c / 2) :
    HasDerivAt (fun s ↦ coleHopfInv β (ξ s x))
      (a * Δ (coleHopfInv β ∘ ξ t) x +
        (c / 2) * ‖∇ (coleHopfInv β ∘ ξ t) x‖ ^ 2 - g) t := by
  let σ : E → ℝ := coleHopfInv β ∘ ξ t
  have hσ : ContDiff ℝ 2 σ := by
    rw [← contDiffOn_univ]
    apply ((contDiffOn_coleHopfInv β).of_le (show (2 : ℕ∞ω) ≤ ∞ from
      WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).comp hspace.contDiffOn
    intro y _
    exact hdomain y
  have htransform : coleHopf β ∘ σ = ξ t := by
    funext y
    exact coleHopf_coleHopfInv (hdomain y)
  have hlap := laplacian_coleHopf_comp_apply β σ hσ x
  rw [htransform] at hlap
  have hderiv := (hasDerivAt_coleHopfInv (hdomain x)).comp t htime
  have hexp : 1 + β * ξ t x = Real.exp (β * σ x) :=
    (exp_mul_coleHopfInv (hdomain x)).symm
  have hcoef : (1 + β * ξ t x)⁻¹ *
      (a * Δ (ξ t) x - (1 + β * ξ t x) * g) =
      a * Δ σ x + (c / 2) * ‖∇ σ x‖ ^ 2 - g := by
    rw [hexp, hlap, ← hcancel]
    field_simp
  rw [hcoef] at hderiv
  exact hderiv

end PDE

end

end Planarwave
