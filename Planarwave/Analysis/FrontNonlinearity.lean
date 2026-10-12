/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontCoefficient
import all Planarwave.Coordinates
import Planarwave.Analysis.InverseModulationNonlinearity
import Planarwave.Analysis.InverseModulationCoordinates
import Planarwave.Analysis.BUCPartialDerivatives

/-!
# The nonlinear estimate for the actual front

Specialize Lemma 4.1 to the challenge's reaction, profile, and transverse
diffusion coefficient. All boundedness and Taylor constants follow from the
original smoothness and end-state hypotheses. The derivative fields used in
the formula are extracted from the full first and second spatial derivatives.
The inverse-modulated PDE itself is a separate obligation.
-/

open scoped Gradient Laplacian ContDiff

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)

local instance : NormedAddCommGroup (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ) (E := (ℝ^m × ℝ) →L[ℝ] ℝ^n)
local instance : NormedAddCommGroup
    (BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)) :=
  BUC.instNormedAddCommGroup (α := ℝ^m × ℝ) (E := (ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n)

/-- The front profile, constant in the transverse variables, is BUC by its two end states. -/
def frontSplitProfileBUC : BUC (ℝ^m × ℝ) (ℝ^n) :=
  (BUC.ofTwoEnded h₂.smooth.continuous
    (tendsto_frontLeftState f D c φ h₂) (tendsto_frontRightState f D c φ h₂)).comp
      Prod.snd uniformContinuous_snd

@[simp]
theorem frontSplitProfileBUC_apply (x : ℝ^m × ℝ) :
    frontSplitProfileBUC f D c φ h₂ x = φ x.2 := rfl

/-- The paper's exact nonlinear remainder for the original challenge data.
`v₁` and `v₂` are the first and second spatial derivative fields in split coordinates. -/
def frontInverseModulationNonlinearity (v : BUC (ℝ^m × ℝ) (ℝ^n))
    (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ) : BUC (ℝ^m × ℝ) (ℝ^n) :=
  inverseModulationNonlinearity f
    (h₁.smooth.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) D c (d_perp D φ ψ)
    (frontSplitProfileBUC f D c φ h₂) v (BUC.longitudinalDerivativeField v₁)
    (BUC.longitudinalSecondDerivativeField v₂) (BUC.mixedDerivativeField v₂) s l g

/-- The concrete formula in terms of the full Fréchet derivative fields. -/
theorem frontInverseModulationNonlinearity_apply (v : BUC (ℝ^m × ℝ) (ℝ^n))
    (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ) (x : ℝ^m × ℝ) :
    frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g x =
      f (φ x.2 + v x) - f (φ x.2) - fderiv ℝ f (φ x.2) (v x) +
        l x.1 • (d_perp D φ ψ • v₁ x (0, 1) - D (v₁ x (0, 1))) +
        ‖s x.1‖ ^ 2 • (D (v₂ x (0, 1) (0, 1)) + (c / 2) • v₁ x (0, 1)) -
        (2 : ℝ) • D (v₂ x (s x.1, 0) (0, 1)) - g x.1 • v₁ x (0, 1) := by
  simp only [frontInverseModulationNonlinearity, inverseModulationNonlinearity_apply,
    frontSplitProfileBUC_apply, BUC.longitudinalDerivativeField_apply,
    BUC.longitudinalSecondDerivativeField_apply, BUC.mixedDerivativeField_apply]

/-- With actual derivative data and the phase gradient/Laplacian, the bundled
nonlinearity is precisely the classical expression in `eq:defN` of the paper. -/
theorem frontInverseModulationNonlinearity_eq_classical
    (v : BUC (ℝ^m × ℝ) (ℝ^n))
    (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
    (hv₁ : ∀ x, HasFDerivAt v (v₁ x) x) (hv₂ : ∀ x, HasFDerivAt v₁ (v₂ x) x)
    (σ : ℝ^m → ℝ) (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ)
    (hs : ∀ y, s y = ∇ σ y) (hl : ∀ y, l y = Δ σ y) (y : ℝ^m) (z : ℝ) :
    frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g (y, z) =
      f (φ z + v (y, z)) - f (φ z) - fderiv ℝ f (φ z) (v (y, z)) +
        Δ σ y • (d_perp D φ ψ • deriv (fun r ↦ v (y, r)) z - D (deriv (fun r ↦ v (y, r)) z)) +
        ‖∇ σ y‖ ^ 2 • (D (deriv (fun r ↦ deriv (fun q ↦ v (y, q)) r) z) +
          (c / 2) • deriv (fun r ↦ v (y, r)) z) -
        (2 : ℝ) • D (fderiv ℝ (fun w ↦ deriv (fun r ↦ v (w, r)) z) y (∇ σ y)) -
        g y • deriv (fun r ↦ v (y, r)) z := by
  have hZ (y : ℝ^m) (z : ℝ) : deriv (fun r ↦ v (y, r)) z =
      BUC.longitudinalDerivativeField v₁ (y, z) :=
    (BUC.hasDerivAt_longitudinalDerivativeField v v₁ hv₁ y z).deriv
  have hZZ : deriv (fun r ↦ deriv (fun q ↦ v (y, q)) r) z =
      BUC.longitudinalSecondDerivativeField v₂ (y, z) := by
    simpa only [hZ] using (BUC.hasDerivAt_longitudinalSecondDerivativeField v₁ v₂ hv₂ y z).deriv
  have hYZ : fderiv ℝ (fun w ↦ deriv (fun r ↦ v (w, r)) z) y =
      BUC.mixedDerivativeField v₂ (y, z) := by
    simpa only [hZ] using (BUC.hasFDerivAt_mixedDerivativeField v₁ v₂ hv₂ y z).fderiv
  rw [hZZ, hYZ, hZ, frontInverseModulationNonlinearity_apply]
  simp only [BUC.longitudinalDerivativeField_apply, BUC.longitudinalSecondDerivativeField_apply,
    BUC.mixedDerivativeField_apply, hs, hl]

/-- Lemma 4.1 for the original front, with the sum norm on two spatial BUC derivatives.
The constant is uniform over the entire fixed-size perturbation ball and all phase/forcing data. -/
theorem exists_frontInverseModulationNonlinearity_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ v : BUC (ℝ^m × ℝ) (ℝ^n),
      ∀ v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n),
      ∀ s : BUC (ℝ^m) (ℝ^m), ∀ l g : BUC (ℝ^m) ℝ, ‖v‖ ≤ R →
      ‖frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g‖ ≤
        C * (‖v‖ ^ 2 + (‖v‖ + ‖v₁‖ + ‖v₂‖) * (‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖)) := by
  obtain ⟨K, hK, hb⟩ := exists_inverseModulationNonlinearity_bound f
    (h₁.smooth.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) D c
    (d_perp D φ ψ) (frontSplitProfileBUC (m := m) f D c φ h₂) hR
  refine ⟨2 * K, by positivity, fun v v₁ v₂ s l g hv ↦ ?_⟩
  have hparts : ‖BUC.longitudinalDerivativeField v₁‖ +
      ‖BUC.longitudinalSecondDerivativeField v₂‖ + ‖BUC.mixedDerivativeField v₂‖ ≤
      2 * (‖v‖ + ‖v₁‖ + ‖v₂‖) := by
    have hfirst := BUC.norm_longitudinalDerivativeField_le v₁
    have hsecond := BUC.norm_longitudinalSecondDerivativeField_le v₂
    have hmixed := BUC.norm_mixedDerivativeField_le v₂
    linarith [norm_nonneg v, norm_nonneg v₁]
  calc
    _ ≤ K * (‖v‖ ^ 2 + (‖BUC.longitudinalDerivativeField v₁‖ +
        ‖BUC.longitudinalSecondDerivativeField v₂‖ + ‖BUC.mixedDerivativeField v₂‖) *
        (‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖)) :=
      hb v _ _ _ s l g hv
    _ ≤ K * (‖v‖ ^ 2 + (2 * (‖v‖ + ‖v₁‖ + ‖v₂‖)) *
        (‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖)) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hK.le (sq_nonneg ‖v‖)]

/-- The inverse-modulated perturbation of actual spatial BUC data, expressed in
the challenge's exact transverse and longitudinal coordinates. -/
def frontInverseModulatedPerturbation {d : ℕ} (hd : 2 ≤ d)
    (u : BUC (ℝ^d) (ℝ^n)) (a : ℝ) (σ : BUC (ℝ^(d - 1)) ℝ) :
    BUC (ℝ^(d - 1) × ℝ) (ℝ^n) :=
  modulationShift a σ
    (u.comp (coordinateEquiv hd).symm (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous) -
    frontSplitProfileBUC f D c φ h₂

/-- Pointwise identification with the paper's `u(y,z+c*t+σ(y)) - φ(z)`. -/
theorem frontInverseModulatedPerturbation_apply {d : ℕ} (hd : 2 ≤ d)
    (u : BUC (ℝ^d) (ℝ^n)) (a : ℝ) (σ : BUC (ℝ^(d - 1)) ℝ) (y : ℝ^(d - 1)) (z : ℝ) :
    frontInverseModulatedPerturbation f D c φ h₂ hd u a σ (y, z) =
      u (full y (z + a + σ y)) - φ z := rfl

/-- The inverse-modulated BUC estimate is exactly the forward physical-space
estimate required by the challenge, with no loss in the constant. -/
theorem norm_frontInverseModulatedPerturbation_le_iff {d : ℕ} (hd : 2 ≤ d)
    (u : BUC (ℝ^d) (ℝ^n)) (a : ℝ) (σ : BUC (ℝ^(d - 1)) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖frontInverseModulatedPerturbation f D c φ h₂ hd u a σ‖ ≤ ε ↔
      ∀ x : ℝ^d, ‖u x - φ (horizontal x - a - σ (transverse x))‖ ≤ ε := by
  have hcomp (x : ℝ^(d - 1) × ℝ) :
      (u.comp (coordinateEquiv hd).symm
        (coordinateEquiv hd).symm.toContinuousLinearMap.uniformContinuous) x =
        u (full x.1 x.2) := rfl
  rw [frontInverseModulatedPerturbation, norm_inverseModulatedPerturbation_eq_forward, BUC.norm_le hε]
  constructor
  · intro h x
    have hx := h (transverse x, horizontal x)
    simpa only [BUC.sub_apply, BUC.add_apply, hcomp,
      modulationShift_apply, frontSplitProfileBUC_apply, BUC.neg_apply,
      full_transverse_horizontal hd, sub_eq_add_neg] using hx
  · intro h x
    have hx := h (full x.1 x.2)
    simpa only [BUC.sub_apply, BUC.add_apply, hcomp,
      modulationShift_apply, frontSplitProfileBUC_apply, BUC.neg_apply,
      horizontal_full hd, transverse_full hd, sub_eq_add_neg] using hx

/-- At the initial zero phase, the inverse-modulated bound is precisely the
original hypothesis `IsCloseToFront`. -/
theorem norm_frontInverseModulatedPerturbation_zero_le_iff {d : ℕ} (hd : 2 ≤ d)
    (u : BUC (ℝ^d) (ℝ^n)) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖frontInverseModulatedPerturbation f D c φ h₂ hd u 0 0‖ ≤ ε ↔ IsCloseToFront φ u ε := by
  simpa only [BUC.zero_apply, sub_zero, IsCloseToFront] using
    norm_frontInverseModulatedPerturbation_le_iff f D c φ h₂ hd u 0 0 hε

end

end Planarwave
