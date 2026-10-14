/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.NinthDerivativeInterpolation
public import Planarwave.Analysis.LogarithmicDecayWeights

@[expose] public section

/-!
# The interpolated tracking bound

Absorb the logarithm using the gap `7/9 - 3/4 = 1/36`, and obtain the
precise amplitude and time powers in `eq:vestC2`. The high-order bound
is an explicit input: deriving it by parabolic regularity is a separate
step, not an assumption added to the challenge theorem.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

/-- The logarithm costs an arbitrarily small positive power of time. -/
theorem log_two_add_le_small_rpow {q t : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    Real.log (2 + t) ≤ (2 / q) * (1 + t) ^ q := by
  have htwo : (2 : ℝ) ^ q ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq1
  calc
    _ ≤ (2 + t) ^ q / q := Real.log_le_rpow_div (by linarith) hq
    _ ≤ (2 * (1 + t)) ^ q / q := by
      apply div_le_div_of_nonneg_right _ hq.le
      exact Real.rpow_le_rpow (by linarith) (by linarith) hq.le
    _ = (2 : ℝ) ^ q * (1 + t) ^ q / q := by rw [Real.mul_rpow (by norm_num) (by linarith)]
    _ ≤ 2 * (1 + t) ^ q / q := by gcongr
    _ = _ := by ring

/-- The interpolation exponent has just enough slack to remove the
logarithm while retaining the paper's `3/4` time decay. -/
theorem tracking_weight_rpow_seven_ninths_le {t : ℝ} (ht : 0 ≤ t) :
    ((1 + t)⁻¹ * Real.log (2 + t)) ^ ((7 : ℝ) / 9) ≤
      (56 : ℝ) ^ ((7 : ℝ) / 9) * (1 + t) ^ (-(3 : ℝ) / 4) := by
  have hden : 0 < 1 + t := by linarith
  have hw : (1 + t)⁻¹ * Real.log (2 + t) ≤ 56 * (1 + t) ^ (-(27 : ℝ) / 28) := by
    have hlog := log_two_add_le_small_rpow (q := (1 : ℝ) / 28) (by norm_num) (by norm_num) ht
    norm_num at hlog
    calc
      _ ≤ (1 + t)⁻¹ * (56 * (1 + t) ^ ((1 : ℝ) / 28)) :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hden.le)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_neg_one, ← Real.rpow_add hden]
        norm_num
  calc
    _ ≤ (56 * (1 + t) ^ (-(27 : ℝ) / 28)) ^ ((7 : ℝ) / 9) :=
      Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hden.le) (Real.log_nonneg (by linarith))) hw (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hden.le _), ← Real.rpow_mul hden.le]
      norm_num

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Step 4's interpolation estimate for genuine spatial derivatives.
The constants and smallness threshold precede the function, amplitude,
and time. It applies wherever the uniform C⁹ bound has been established. -/
theorem exists_tracking_c2_interpolation_bound {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ ε > 0, ∀ (M t : ℝ) (f : E → F), M ∈ Icc 0 ε → 0 ≤ t →
      ContDiff ℝ 9 f →
      (∀ k ≤ 9, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k f x‖)) →
      (∀ x, ‖f x‖ ≤ K * M / (1 + t) * Real.log (2 + t)) →
      (∀ x, ‖iteratedFDeriv ℝ 9 f x‖ ≤ B) →
      derivativeSupNorm f 0 + derivativeSupNorm f 1 + derivativeSupNorm f 2 ≤
        C * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4) := by
  let J := 1 + 2 * (8 : ℝ) ^ 36 * (1 + B)
  have hJ : 0 < J := by dsimp only [J]; positivity
  let C := J * ((56 * K) ^ ((7 : ℝ) / 9)) + 1
  let ε := min 1 (1 / (4 * (K + 1)))
  refine ⟨C, by dsimp only [C]; positivity, ε, by dsimp only [ε]; positivity, ?_⟩
  intro M t f hM ht hf hb hzero hnine
  have hM0 : 0 ≤ M := hM.1
  have hM1 : M ≤ 1 := hM.2.trans (min_le_left _ _)
  have hsmall : K * M ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (K + 1))).mp (hM.2.trans (min_le_right _ _))
    nlinarith
  let w := (1 + t)⁻¹ * Real.log (2 + t)
  let A := (K * M) * w
  have hden : 0 < 1 + t := by linarith
  have hw : 0 ≤ w := mul_nonneg (inv_nonneg.mpr hden.le) (Real.log_nonneg (by linarith))
  have hw4 : w ≤ 4 := by
    have h := inverse_mul_log_two_add_le_half_decay ht
    rw [Real.rpow_neg_one] at h
    have hp : (1 + t) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    exact h.trans (by nlinarith)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hA1 : A ≤ 1 := by dsimp only [A]; nlinarith
  have hnorm := derivativeSupNorm_c2_le_of_nine hf hb hA0 hA1 hB
    (fun x ↦ (hzero x).trans_eq (by dsimp only [A, w]; rw [div_eq_mul_inv]; ring)) hnine
  have hpow : A ^ ((7 : ℝ) / 9) ≤
      (56 * K) ^ ((7 : ℝ) / 9) * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4) := by
    have hMp : M ^ ((7 : ℝ) / 9) ≤ M ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_ge' hM0 hM1 (by norm_num) (by norm_num)
    calc
      _ = (K ^ ((7 : ℝ) / 9) * M ^ ((7 : ℝ) / 9)) * w ^ ((7 : ℝ) / 9) := by
        dsimp only [A]
        rw [Real.mul_rpow (mul_nonneg hK hM0) hw, Real.mul_rpow hK hM0]
      _ ≤ (K ^ ((7 : ℝ) / 9) * M ^ ((3 : ℝ) / 4)) *
          ((56 : ℝ) ^ ((7 : ℝ) / 9) * (1 + t) ^ (-(3 : ℝ) / 4)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hMp (Real.rpow_nonneg hK _))
          (tracking_weight_rpow_seven_ninths_le ht) (Real.rpow_nonneg hw _) (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hK]; ring
  calc
    _ ≤ J * A ^ ((7 : ℝ) / 9) := hnorm
    _ ≤ J * ((56 * K) ^ ((7 : ℝ) / 9) * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hpow hJ.le
    _ ≤ C * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4) := by
      dsimp only [C]
      nlinarith [mul_nonneg (Real.rpow_nonneg hM0 ((3 : ℝ) / 4))
        (Real.rpow_nonneg hden.le (-(3 : ℝ) / 4))]

local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance : NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] F)) := inferInstance

/-- Identify the norms of supplied genuine BUC derivatives with the
supremum norms used by the interpolation argument. -/
theorem norm_buc_c2_le_derivativeSupNorm (v : BUC E F) (v₁ : BUC E (E →L[ℝ] F))
    (v₂ : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hv₁ : ∀ x, HasFDerivAt v (v₁ x) x) (hv₂ : ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (hb : ∀ k ≤ 2, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k v x‖)) :
    ‖v‖ + ‖v₁‖ + ‖v₂‖ ≤ derivativeSupNorm v 0 + derivativeSupNorm v 1 + derivativeSupNorm v 2 := by
  have h0 : ‖v‖ ≤ derivativeSupNorm v 0 := by
    apply (BUC.norm_le (derivativeSupNorm_nonneg v 0 (hb 0 (by omega)))).mpr
    intro x
    simpa only [norm_iteratedFDeriv_zero] using norm_iteratedFDeriv_le_derivativeSupNorm v 0 (hb 0 (by omega)) x
  have h1 : ‖v₁‖ ≤ derivativeSupNorm v 1 := by
    apply (BUC.norm_le (derivativeSupNorm_nonneg v 1 (hb 1 (by omega)))).mpr
    intro x
    have h := norm_iteratedFDeriv_le_derivativeSupNorm v 1 (hb 1 (by omega)) x
    simpa only [norm_iteratedFDeriv_one, (hv₁ x).fderiv] using h
  have h2 : ‖v₂‖ ≤ derivativeSupNorm v 2 := by
    have hfun : (v₁ : E → E →L[ℝ] F) = fderiv ℝ v := funext fun x ↦ (hv₁ x).fderiv.symm
    apply (BUC.norm_le (derivativeSupNorm_nonneg v 2 (hb 2 le_rfl))).mpr
    intro x
    have h := norm_iteratedFDeriv_le_derivativeSupNorm v 2 (hb 2 le_rfl) x
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one, ← hfun, (hv₂ x).fderiv] at h
    exact h
  exact add_le_add (add_le_add h0 h1) h2

/-- The interpolated bound in precisely the BUC two-jet norm appearing
in `exists_frontInverseModulationNonlinearity_bound`. -/
theorem exists_tracking_buc_c2_interpolation_bound {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ ε > 0, ∀ (M t : ℝ) (v : BUC E F) (v₁ : BUC E (E →L[ℝ] F))
      (v₂ : BUC E (E →L[ℝ] E →L[ℝ] F)),
      M ∈ Icc 0 ε → 0 ≤ t → ContDiff ℝ 9 (v : E → F) →
      (∀ x, HasFDerivAt v (v₁ x) x) → (∀ x, HasFDerivAt v₁ (v₂ x) x) →
      (∀ k ≤ 9, BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ k v x‖)) →
      ‖v‖ ≤ K * M / (1 + t) * Real.log (2 + t) →
      (∀ x, ‖iteratedFDeriv ℝ 9 v x‖ ≤ B) →
      ‖v‖ + ‖v₁‖ + ‖v₂‖ ≤ C * M ^ ((3 : ℝ) / 4) * (1 + t) ^ (-(3 : ℝ) / 4) := by
  obtain ⟨C, hC, ε, hε, hi⟩ := exists_tracking_c2_interpolation_bound (E := E) (F := F) hK hB
  refine ⟨C, hC, ε, hε, ?_⟩
  intro M t v v₁ v₂ hM ht hv hv₁ hv₂ hb hzero hnine
  exact (norm_buc_c2_le_derivativeSupNorm v v₁ v₂ hv₁ hv₂ (fun k hk ↦ hb k (by omega))).trans
    (hi M t v hM ht hv hb (fun x ↦ (v.norm_apply_le x).trans hzero) hnine)

end

end Planarwave
