/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamel
public import Planarwave.Analysis.SemigroupDuhamel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# Heat Volterra equations with time-dependent bounded coefficients

The Cole--Hopf equation has a time-dependent multiplication coefficient.
We construct its Volterra operator on continuous BUC-valued paths and
prove factorial decay of the iterated operator norms. The convergent
Neumann series then solves the inhomogeneous mild equation on every
finite interval, without a smallness condition on the time horizon.
-/

open Filter MeasureTheory Set Topology
open C0Semigroup (TimePath extendTimePath continuous_extendTimePath extendTimePath_coe)

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The nonautonomous heat Volterra term on a compact time interval. -/
def heatVolterraPath (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (u : TimePath (E := BUC E F) T) : TimePath (E := BUC E F) T where
  toFun t := heatDuhamel a (fun r ↦ extendTimePath B r (extendTimePath u r)) t
  continuous_toFun := (continuous_heatDuhamel a
    ((continuous_extendTimePath B).clm_apply (continuous_extendTimePath u))).comp
      continuous_subtype_val

theorem norm_heatVolterraPath_le (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (u : TimePath (E := BUC E F) T) :
    ‖heatVolterraPath a B u‖ ≤ (‖B‖ * T) * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    ‖heatVolterraPath a B u t‖ ≤ (‖B‖ * ‖u‖) * (t : ℝ) :=
      norm_heatDuhamel_le _ t.2.1 (fun r _ ↦
        ((extendTimePath B r).le_opNorm _).trans
          (mul_le_mul (B.norm_coe_le_norm _) (u.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)))
    _ ≤ (‖B‖ * ‖u‖) * (T : ℝ) := by gcongr; exact t.2.2
    _ = _ := by ring

theorem heatVolterraPath_add (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (u v : TimePath (E := BUC E F) T) :
    heatVolterraPath a B (u + v) = heatVolterraPath a B u + heatVolterraPath a B v := by
  apply ContinuousMap.ext
  intro t
  change heatDuhamel a (fun r ↦ extendTimePath B r (extendTimePath (u + v) r)) t =
    heatDuhamel a (fun r ↦ extendTimePath B r (extendTimePath u r)) t +
      heatDuhamel a (fun r ↦ extendTimePath B r (extendTimePath v r)) t
  simpa only [extendTimePath, ContinuousMap.add_apply, map_add] using!
    heatDuhamel_add a
      ((continuous_extendTimePath B).clm_apply (continuous_extendTimePath u))
      ((continuous_extendTimePath B).clm_apply (continuous_extendTimePath v)) t

theorem heatVolterraPath_smul (a c : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (u : TimePath (E := BUC E F) T) :
    heatVolterraPath a B (c • u) = c • heatVolterraPath a B u := by
  apply ContinuousMap.ext
  intro t
  change heatDuhamel a (fun r ↦ extendTimePath B r (extendTimePath (c • u) r)) t =
    c • heatDuhamel a (fun r ↦ extendTimePath B r (extendTimePath u r)) t
  simpa only [extendTimePath, ContinuousMap.smul_apply, map_smul] using!
    heatDuhamel_smul a c (fun r ↦ extendTimePath B r (extendTimePath u r)) t

/-- The Volterra operator is bounded and linear in the unknown trajectory. -/
def heatVolterraOperator (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T) :
    TimePath (E := BUC E F) T →L[ℝ] TimePath (E := BUC E F) T :=
  LinearMap.mkContinuous
    { toFun := heatVolterraPath a B
      map_add' := heatVolterraPath_add a B
      map_smul' := fun c u ↦ heatVolterraPath_smul a c B u }
    (‖B‖ * T) (norm_heatVolterraPath_le a B)

@[simp]
theorem heatVolterraOperator_apply (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (u : TimePath (E := BUC E F) T) :
    heatVolterraOperator a B u = heatVolterraPath a B u := rfl

/-- Each iteration gains one power of time and one factorial denominator,
even though the coefficient depends on time. -/
theorem norm_heatVolterraOperator_pow_apply_le (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (u : TimePath (E := BUC E F) T) (n : ℕ) (t : Icc (0 : ℝ) (T : ℝ)) :
    ‖((heatVolterraOperator a B) ^ n) u t‖ ≤
      (‖B‖ ^ n / n.factorial) * ‖u‖ * (t : ℝ) ^ n := by
  induction n generalizing t with
  | zero => simpa using u.norm_coe_le_norm t
  | succ n ih =>
    let v := ((heatVolterraOperator a B) ^ n) u
    have hint : IntervalIntegrable
        (fun r : ℝ ↦ ((‖B‖ ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n) volume 0 t :=
      (by fun_prop : Continuous
        (fun r : ℝ ↦ ((‖B‖ ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n)).intervalIntegrable 0 t
    have hnorm : ‖heatVolterraPath a B v t‖ ≤
        ∫ r in (0 : ℝ)..(t : ℝ), ((‖B‖ ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n := by
      change ‖∫ r in (0 : ℝ)..(t : ℝ),
        heatFlowBUC a ((t : ℝ) - r) (extendTimePath B r (extendTimePath v r))‖ ≤ _
      apply intervalIntegral.norm_integral_le_of_norm_le t.2.1 _ hint
      filter_upwards [] with r hr
      have hrT : r ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hr.1.le, hr.2.trans t.2.2⟩
      have hvr : ‖extendTimePath v r‖ ≤ (‖B‖ ^ n / n.factorial) * ‖u‖ * r ^ n := by
        rw [show extendTimePath v r = v ⟨r, hrT⟩ from extendTimePath_coe v ⟨r, hrT⟩]
        exact ih ⟨r, hrT⟩
      calc
        _ ≤ ‖extendTimePath B r (extendTimePath v r)‖ := norm_heatFlowBUC_le _ _ _
        _ ≤ ‖extendTimePath B r‖ * ‖extendTimePath v r‖ := (extendTimePath B r).le_opNorm _
        _ ≤ ‖B‖ * ((‖B‖ ^ n / n.factorial) * ‖u‖ * r ^ n) :=
          mul_le_mul (B.norm_coe_le_norm _) hvr (norm_nonneg _) (norm_nonneg _)
        _ = _ := by rw [pow_succ]; ring
    have heval : (∫ r in (0 : ℝ)..(t : ℝ),
        ((‖B‖ ^ (n + 1) / n.factorial) * ‖u‖) * r ^ n) =
        (‖B‖ ^ (n + 1) / (n + 1).factorial) * ‖u‖ * (t : ℝ) ^ (n + 1) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
    rw [heval] at hnorm
    simpa only [pow_succ', mul_apply_eq_comp, heatVolterraOperator_apply] using hnorm

/-- A summable majorant for the iterated operator norms on any finite interval. -/
theorem norm_heatVolterraOperator_pow_le (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T) (n : ℕ) :
    ‖(heatVolterraOperator a B) ^ n‖ ≤ (‖B‖ * (T : ℝ)) ^ n / n.factorial := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    _ ≤ (‖B‖ ^ n / n.factorial) * ‖u‖ * (t : ℝ) ^ n :=
      norm_heatVolterraOperator_pow_apply_le a B u n t
    _ ≤ (‖B‖ ^ n / n.factorial) * ‖u‖ * (T : ℝ) ^ n := by
      gcongr
      · exact t.2.1
      · exact t.2.2
    _ = _ := by rw [mul_pow]; ring

theorem summable_heatVolterraOperator_pow (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T) :
    Summable (fun n : ℕ ↦ (heatVolterraOperator a B) ^ n) := by
  apply Summable.of_norm_bounded (f := fun n : ℕ ↦ (heatVolterraOperator a B) ^ n)
    (Real.summable_pow_div_factorial (‖B‖ * (T : ℝ)))
  exact norm_heatVolterraOperator_pow_le a B

/-- Invertibility of `I - V`, proved by the convergent Volterra series. -/
theorem isUnit_one_sub_heatVolterraOperator (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T) :
    IsUnit (1 - heatVolterraOperator a B) := by
  let : IsTopologicalRing (TimePath (E := BUC E F) T →L[ℝ] TimePath (E := BUC E F) T) :=
    NonUnitalSeminormedRing.toIsTopologicalRing
      (α := TimePath (E := BUC E F) T →L[ℝ] TimePath (E := BUC E F) T)
  have hs := summable_heatVolterraOperator_pow a B
  exact ⟨⟨1 - heatVolterraOperator a B, ∑' n : ℕ, (heatVolterraOperator a B) ^ n,
    hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩, rfl⟩

/-- Existence and uniqueness for the inhomogeneous heat Volterra equation
on every finite time horizon, with no smallness assumption. -/
theorem existsUnique_heatVolterraPath (a : ℝ) {T : NNReal}
    (B : TimePath (E := BUC E F →L[ℝ] BUC E F) T)
    (f : TimePath (E := BUC E F) T) :
    ∃! u : TimePath (E := BUC E F) T, ∀ t, u t = f t + heatVolterraPath a B u t := by
  have hbij : Function.Bijective
      (1 - heatVolterraOperator a B : TimePath (E := BUC E F) T →L[ℝ] TimePath (E := BUC E F) T) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_heatVolterraOperator a B)
  obtain ⟨u, hu⟩ := hbij.surjective f
  refine ⟨u, ?_, ?_⟩
  · intro t
    have h := congrArg (fun v : TimePath (E := BUC E F) T ↦ v t) hu
    change u t - heatVolterraPath a B u t = f t at h
    exact sub_eq_iff_eq_add.mp h
  · intro v hv
    apply hbij.injective
    rw [hu]
    apply ContinuousMap.ext
    intro t
    change v t - heatVolterraPath a B v t = f t
    exact sub_eq_iff_eq_add.mpr (hv t)

end

end Planarwave
