/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.LongitudinalPairingDerivative
public import Planarwave.Analysis.HeatDivergenceSmoothing

@[expose] public section

/-!
# The divergence form of the projected nonlinearity

The exact rewriting in the proof of Lemma 4.2, with actual derivative
witnesses. The weight and its first two derivatives are assumed integrable
here. Deriving such an adjoint representative from the spectral assumptions
remains a separate obligation; this module does not add assumptions to the
challenge theorem.
-/

open MeasureTheory

namespace Planarwave

noncomputable section

variable {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The mixed derivative is a divergence minus the scalar divergence correction. -/
theorem longitudinalPairing_mixed_eq_flux {ψ ψ₁ : ℝ → F}
    (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z)
    (v vz : BUC (Y × ℝ) F) (vy vyz : BUC (Y × ℝ) (Y →L[ℝ] F))
    (hvz : ∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z)
    (hvy : ∀ y z, HasFDerivAt (fun w ↦ v (w, z)) (vy (y, z)) y)
    (hvyz : ∀ y z, HasFDerivAt (fun w ↦ vz (w, z)) (vyz (y, z)) y)
    (s : BUC Y Y) (s₁ : BUC Y (Y →L[ℝ] Y)) :
    longitudinalPairing ψ hψ (BUC.operatorApply vyz (transverseLift s)) =
      -divergenceBUC (fluxDerivativeBUC (longitudinalPairing ψ₁ hψ₁ v)
        (longitudinalPairingDerivative ψ₁ hψ₁ vy) s s₁) +
      BUC.smulBUC (divergenceBUC s₁) (longitudinalPairing ψ₁ hψ₁ v) := by
  rw [longitudinalPairing_operatorApply,
    longitudinalPairing_mixedDerivative hψ hψ₁ hderiv v vz vy vyz hvz hvy hvyz,
    divergenceBUC_fluxDerivative]
  ext y
  simp only [BUC.operatorApply_apply, BUC.neg_apply, neg_apply,
    BUC.add_apply, BUC.smulBUC_apply, smul_eq_mul]
  ring

variable [ProperSpace F]

/-- The full six-term identity displayed in the proof of Lemma 4.2.
Here `s = ∇σ` and `div s = Δσ` when applied to a phase. -/
theorem longitudinalPairing_inverseModulationNonlinearity
    (f : F → F) (hf : ContDiff ℝ 2 f) (D : F →L[ℝ] F) (c a : ℝ)
    {ψ ψ₁ ψ₂ : ℝ → F} (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁) (hψ₂ : Integrable ψ₂)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z) (hderiv₁ : ∀ z, HasDerivAt ψ₁ (ψ₂ z) z)
    (p v vz vzz : BUC (Y × ℝ) F) (vy vyz : BUC (Y × ℝ) (Y →L[ℝ] F))
    (hvz : ∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z)
    (hvzz : ∀ y z, HasDerivAt (fun r ↦ vz (y, r)) (vzz (y, z)) z)
    (hvy : ∀ y z, HasFDerivAt (fun w ↦ v (w, z)) (vy (y, z)) y)
    (hvyz : ∀ y z, HasFDerivAt (fun w ↦ vz (w, z)) (vyz (y, z)) y)
    (s : BUC Y Y) (s₁ : BUC Y (Y →L[ℝ] Y)) (g : BUC Y ℝ) :
    let l := divergenceBUC s₁
    let P₁ := longitudinalPairing ψ₁ hψ₁ v
    let Q₁ := longitudinalPairing ψ₁ hψ₁ (BUC.postcompCLM D v)
    let Q₂ := longitudinalPairing ψ₂ hψ₂ (BUC.postcompCLM D v)
    let Qy := longitudinalPairingDerivative ψ₁ hψ₁ (BUC.postcompCLM (D.postcomp Y) vy)
    longitudinalPairing ψ hψ (inverseModulationNonlinearity f hf D c a p v vz vzz vyz s l g) =
      longitudinalPairing ψ hψ (BUC.reactionRemainder f hf p v) -
        BUC.smulBUC l (a • P₁ - Q₁) +
        BUC.smulBUC (phaseGradientSquared s) (Q₂ - (c / 2) • P₁) +
        (2 : ℝ) • divergenceBUC (fluxDerivativeBUC Q₁ Qy s s₁) -
        (2 : ℝ) • BUC.smulBUC l Q₁ + BUC.smulBUC g P₁ := by
  dsimp only
  have hDz (y : Y) (z : ℝ) := D.hasFDerivAt.comp_hasDerivAt z (hvz y z)
  have hDzz (y : Y) (z : ℝ) := D.hasFDerivAt.comp_hasDerivAt z (hvzz y z)
  have hDy (y : Y) (z : ℝ) := D.hasFDerivAt.comp y (hvy y z)
  have hDyz (y : Y) (z : ℝ) := D.hasFDerivAt.comp y (hvyz y z)
  have hfirst := longitudinalPairing_derivative hψ hψ₁ hderiv v vz hvz
  have hDfirst := longitudinalPairing_derivative hψ hψ₁ hderiv
    (BUC.postcompCLM D v) (BUC.postcompCLM D vz) hDz
  have hDsecond := longitudinalPairing_secondDerivative hψ hψ₁ hψ₂ hderiv hderiv₁
    (BUC.postcompCLM D v) (BUC.postcompCLM D vz) (BUC.postcompCLM D vzz) hDz hDzz
  have hmixed := longitudinalPairing_mixed_eq_flux hψ hψ₁ hderiv
    (BUC.postcompCLM D v) (BUC.postcompCLM D vz)
    (BUC.postcompCLM (𝕜 := ℝ) (E := Y →L[ℝ] F) (F := Y →L[ℝ] F) (D.postcomp Y) vy)
    (BUC.postcompCLM (𝕜 := ℝ) (E := Y →L[ℝ] F) (F := Y →L[ℝ] F) (D.postcomp Y) vyz)
    hDz hDy hDyz s s₁
  have hDapply : BUC.postcompCLM D (BUC.operatorApply vyz (transverseLift s)) =
      BUC.operatorApply
        (BUC.postcompCLM (𝕜 := ℝ) (E := Y →L[ℝ] F) (F := Y →L[ℝ] F) (D.postcomp Y) vyz)
        (transverseLift s) := by
    ext x
    rfl
  simp only [inverseModulationNonlinearity, map_add, map_sub, map_smul,
    longitudinalPairing_smul, hfirst, hDfirst, hDsecond, hDapply, hmixed]
  ext y
  simp only [BUC.add_apply, BUC.sub_apply, BUC.neg_apply, BUC.smul_apply,
    BUC.smulBUC_apply, smul_eq_mul]
  ring

variable [MeasurableSpace Y] [BorelSpace Y]

/-- Term-by-term estimate of the divergence form. Only the flux term uses
heat smoothing; every other term uses the heat contraction. -/
theorem norm_heatFlowBUC_divergenceForm_le {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (c a : ℝ) (r P Q U : BUC Y ℝ) (Qy : BUC Y (Y →L[ℝ] ℝ))
    (s : BUC Y Y) (s₁ : BUC Y (Y →L[ℝ] Y)) (g : BUC Y ℝ)
    (hQ : ∀ y, HasFDerivAt Q (Qy y) y) (hs : ∀ y, HasFDerivAt s (s₁ y) y) :
    let l := divergenceBUC s₁
    ‖heatFlowBUC b t (r - BUC.smulBUC l (a • P - Q) +
      BUC.smulBUC (phaseGradientSquared s) (U - (c / 2) • P) +
      (2 : ℝ) • divergenceBUC (fluxDerivativeBUC Q Qy s s₁) -
      (2 : ℝ) • BUC.smulBUC l Q + BUC.smulBUC g P)‖ ≤
      ‖r‖ + ‖l‖ * (|a| * ‖P‖ + ‖Q‖) +
        ‖s‖ ^ 2 * (‖U‖ + |c / 2| * ‖P‖) +
        2 * ((Module.finrank ℝ Y : ℝ) / heatScale b t) * ‖Q‖ * ‖s‖ +
        2 * ‖l‖ * ‖Q‖ + ‖g‖ * ‖P‖ := by
  dsimp only
  let T := heatOperator (E := Y) (F := ℝ) b t
  have hT (w : BUC Y ℝ) : ‖T w‖ ≤ ‖w‖ := norm_heatFlowBUC_le b t w
  have hL : ‖T (BUC.smulBUC (divergenceBUC s₁) (a • P - Q))‖ ≤
      ‖divergenceBUC s₁‖ * (|a| * ‖P‖ + ‖Q‖) := by
    apply (hT _).trans ((BUC.norm_smulBUC_le _ _).trans ?_)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sub_le (a • P) Q
  have hS : ‖T (BUC.smulBUC (phaseGradientSquared s) (U - (c / 2) • P))‖ ≤
      ‖s‖ ^ 2 * (‖U‖ + |c / 2| * ‖P‖) := by
    apply (hT _).trans ((BUC.norm_smulBUC_le _ _).trans ?_)
    apply mul_le_mul (norm_phaseGradientSquared_le s) _ (norm_nonneg _) (sq_nonneg _)
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sub_le U ((c / 2) • P)
  have hflux : ‖(2 : ℝ) • T (divergenceBUC (fluxDerivativeBUC Q Qy s s₁))‖ ≤
      2 * ((Module.finrank ℝ Y : ℝ) / heatScale b t) * ‖Q‖ * ‖s‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * (((Module.finrank ℝ Y : ℝ) / heatScale b t) * ‖Q‖ * ‖s‖) :=
        mul_le_mul_of_nonneg_left
          (norm_heatFlowBUC_divergence_smul_le hb ht Q s _
            (hasFDerivAt_fluxDerivativeBUC Q Qy s s₁ hQ hs)) (by norm_num)
      _ = _ := by ring
  have hcorr : ‖(2 : ℝ) • T (BUC.smulBUC (divergenceBUC s₁) Q)‖ ≤
      2 * ‖divergenceBUC s₁‖ * ‖Q‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hT _).trans (BUC.norm_smulBUC_le _ _)) (by norm_num)
  have hg : ‖T (BUC.smulBUC g P)‖ ≤ ‖g‖ * ‖P‖ :=
    (hT _).trans (BUC.norm_smulBUC_le _ _)
  change ‖T _‖ ≤ _
  simp only [map_add, map_sub, map_smul]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add (hT r) hL)) hS)) hflux)) hcorr)) hg)

/-- Lemma 4.2 for an integrable twice differentiable weight. The constant is
chosen before all perturbation, phase, and forcing fields; neither a first nor
a second perturbation derivative norm occurs on the right hand side. -/
theorem exists_smoothedProjectedNonlinearity_bound
    (f : F → F) (hf : ContDiff ℝ 2 f) (D : F →L[ℝ] F) (c a : ℝ)
    {ψ ψ₁ ψ₂ : ℝ → F} (hψ : Integrable ψ) (hψ₁ : Integrable ψ₁) (hψ₂ : Integrable ψ₂)
    (hderiv : ∀ z, HasDerivAt ψ (ψ₁ z) z) (hderiv₁ : ∀ z, HasDerivAt ψ₁ (ψ₂ z) z)
    (p : BUC (Y × ℝ) F) {R b t : ℝ} (hR : 0 ≤ R) (hb : 0 < b) (ht : 0 < t) :
    ∃ C > 0, ∀ v vz vzz : BUC (Y × ℝ) F, ∀ vy vyz : BUC (Y × ℝ) (Y →L[ℝ] F),
      ∀ s : BUC Y Y, ∀ s₁ : BUC Y (Y →L[ℝ] Y), ∀ g : BUC Y ℝ,
      (∀ y z, HasDerivAt (fun r ↦ v (y, r)) (vz (y, z)) z) →
      (∀ y z, HasDerivAt (fun r ↦ vz (y, r)) (vzz (y, z)) z) →
      (∀ y z, HasFDerivAt (fun w ↦ v (w, z)) (vy (y, z)) y) →
      (∀ y z, HasFDerivAt (fun w ↦ vz (w, z)) (vyz (y, z)) y) →
      (∀ y, HasFDerivAt s (s₁ y) y) → ‖v‖ ≤ R →
      ‖heatFlowBUC b t (longitudinalPairing ψ hψ
        (inverseModulationNonlinearity f hf D c a p v vz vzz vyz s (divergenceBUC s₁) g))‖ ≤
        C * ‖v‖ * (‖v‖ + ‖divergenceBUC s₁‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖) := by
  obtain ⟨K, hK, hquad⟩ := BUC.exists_reactionRemainder_bound f hf p hR
  let A₀ := ∫ z, ‖ψ z‖
  let A₁ := ∫ z, ‖ψ₁ z‖
  let A₂ := ∫ z, ‖ψ₂ z‖
  let H := (Module.finrank ℝ Y : ℝ) / heatScale b t
  have hA₀ : 0 ≤ A₀ := integral_nonneg fun _ ↦ norm_nonneg _
  have hA₁ : 0 ≤ A₁ := integral_nonneg fun _ ↦ norm_nonneg _
  have hA₂ : 0 ≤ A₂ := integral_nonneg fun _ ↦ norm_nonneg _
  have hH : 0 ≤ H := div_nonneg (Nat.cast_nonneg _) (heatScale_pos_of_pos hb ht).le
  let K₀ := A₀ * K
  let Kl := A₁ * (|a| + 3 * ‖D‖)
  let Ks := 2 * H * A₁ * ‖D‖
  let Kss := A₂ * ‖D‖ + |c / 2| * A₁
  have hK₀ : 0 ≤ K₀ := mul_nonneg hA₀ hK.le
  have hKl : 0 ≤ Kl := by dsimp [Kl]; positivity
  have hKs : 0 ≤ Ks := by dsimp [Ks]; positivity
  have hKss : 0 ≤ Kss := by dsimp [Kss]; positivity
  let C := K₀ + Kl + Ks + Kss + A₁ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hK₀C : K₀ ≤ C := by dsimp [C]; linarith
  have hKlC : Kl ≤ C := by dsimp [C]; linarith
  have hKsC : Ks ≤ C := by dsimp [C]; linarith
  have hKssC : Kss ≤ C := by dsimp [C]; linarith
  have hA₁C : A₁ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun v vz vzz vy vyz s s₁ g hvz hvzz hvy hvyz hs hv ↦ ?_⟩
  let r := longitudinalPairing ψ hψ (BUC.reactionRemainder f hf p v)
  let P := longitudinalPairing ψ₁ hψ₁ v
  let Q := longitudinalPairing ψ₁ hψ₁ (BUC.postcompCLM D v)
  let U := longitudinalPairing ψ₂ hψ₂ (BUC.postcompCLM D v)
  let Qy := longitudinalPairingDerivative ψ₁ hψ₁
    (BUC.postcompCLM (𝕜 := ℝ) (E := Y →L[ℝ] F) (F := Y →L[ℝ] F) (D.postcomp Y) vy)
  have hQ : ∀ y, HasFDerivAt Q (Qy y) y :=
    hasFDerivAt_longitudinalPairing ψ₁ hψ₁ (BUC.postcompCLM D v) _
      (fun y z ↦ D.hasFDerivAt.comp y (hvy y z))
  have hr : ‖r‖ ≤ A₀ * (K * ‖v‖ ^ 2) :=
    (norm_longitudinalPairing_le ψ hψ _).trans
      (mul_le_mul_of_nonneg_left (hquad v hv) hA₀)
  have hP : ‖P‖ ≤ A₁ * ‖v‖ := norm_longitudinalPairing_le ψ₁ hψ₁ v
  have hQnorm : ‖Q‖ ≤ A₁ * ‖D‖ * ‖v‖ := by
    rw [mul_assoc]
    exact (norm_longitudinalPairing_le ψ₁ hψ₁ _).trans
      (mul_le_mul_of_nonneg_left (BUC.norm_postcompCLM_apply_le D v) hA₁)
  have hU : ‖U‖ ≤ A₂ * ‖D‖ * ‖v‖ := by
    rw [mul_assoc]
    exact (norm_longitudinalPairing_le ψ₂ hψ₂ _).trans
      (mul_le_mul_of_nonneg_left (BUC.norm_postcompCLM_apply_le D v) hA₂)
  rw [longitudinalPairing_inverseModulationNonlinearity f hf D c a hψ hψ₁ hψ₂
    hderiv hderiv₁ p v vz vzz vy vyz hvz hvzz hvy hvyz s s₁ g]
  calc
    _ ≤ ‖r‖ + ‖divergenceBUC s₁‖ * (|a| * ‖P‖ + ‖Q‖) +
        ‖s‖ ^ 2 * (‖U‖ + |c / 2| * ‖P‖) + 2 * H * ‖Q‖ * ‖s‖ +
        2 * ‖divergenceBUC s₁‖ * ‖Q‖ + ‖g‖ * ‖P‖ :=
      norm_heatFlowBUC_divergenceForm_le hb ht c a r P Q U Qy s s₁ g hQ hs
    _ ≤ A₀ * (K * ‖v‖ ^ 2) +
        ‖divergenceBUC s₁‖ * (|a| * (A₁ * ‖v‖) + A₁ * ‖D‖ * ‖v‖) +
        ‖s‖ ^ 2 * (A₂ * ‖D‖ * ‖v‖ + |c / 2| * (A₁ * ‖v‖)) +
        2 * H * (A₁ * ‖D‖ * ‖v‖) * ‖s‖ +
        2 * ‖divergenceBUC s₁‖ * (A₁ * ‖D‖ * ‖v‖) + ‖g‖ * (A₁ * ‖v‖) := by
      gcongr
    _ = K₀ * ‖v‖ ^ 2 + Kl * ‖divergenceBUC s₁‖ * ‖v‖ +
        Ks * ‖s‖ * ‖v‖ + Kss * ‖s‖ ^ 2 * ‖v‖ + A₁ * ‖g‖ * ‖v‖ := by
      dsimp [K₀, Kl, Ks, Kss]
      ring
    _ ≤ C * ‖v‖ ^ 2 + C * ‖divergenceBUC s₁‖ * ‖v‖ +
        C * ‖s‖ * ‖v‖ + C * ‖s‖ ^ 2 * ‖v‖ + C * ‖g‖ * ‖v‖ := by
      gcongr
    _ = _ := by ring

end

end Planarwave
