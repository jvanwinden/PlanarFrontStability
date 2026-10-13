/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontProjectedNonlinearity
import Planarwave.Analysis.LogarithmicDecayWeights

/-!
# Quadratic decay of the smoothed front nonlinearity

Step 5 of `lem:key`: substitute the phase and tracking estimates into
Lemma 4.2 to obtain `M² (1+t)^(-3/2) log(2+t)`. There are no perturbation
derivative norms in the estimate. Derivative witnesses are required only
at positive times when the lemma is used along a continuous source path.
-/

open MeasureTheory Set
open scoped Gradient Laplacian

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The derivative-free nonlinear estimate gains a quadratic amplitude
and an integrable decay weight from the low-order tracking estimates. -/
theorem exists_frontSmoothedNonlinearity_decay {R K : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K) :
    ∃ C > 0, ∀ (M t : ℝ) (v : BUC (ℝ^m × ℝ) (ℝ^n))
      (v₁ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] ℝ^n))
      (v₂ : BUC (ℝ^m × ℝ) ((ℝ^m × ℝ) →L[ℝ] (ℝ^m × ℝ) →L[ℝ] ℝ^n))
      (σ : ℝ^m → ℝ) (s : BUC (ℝ^m) (ℝ^m))
      (s₁ : BUC (ℝ^m) (ℝ^m →L[ℝ] ℝ^m)) (l g : BUC (ℝ^m) ℝ),
      0 ≤ M → M ≤ 1 → 0 ≤ t →
      (∀ x, HasFDerivAt v (v₁ x) x) → (∀ x, HasFDerivAt v₁ (v₂ x) x) →
      (∀ y, s y = ∇ σ y) → (∀ y, HasFDerivAt s (s₁ y) y) → (∀ y, l y = Δ σ y) → ‖v‖ ≤ R →
      ‖v‖ ≤ K * M / (1 + t) * Real.log (2 + t) →
      ‖s‖ ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)) →
      ‖l‖ ≤ K * M * (1 + t) ^ (-(1 : ℝ)) →
      ‖g‖ ≤ K * M * (1 + t) ^ (-(5 : ℝ) / 4) →
      ‖heatFlowBUC (d_perp D φ ψ) (1 / 8)
        (longitudinalPairing ψ h₃.integrable
          (frontInverseModulationNonlinearity f D c φ ψ h₁ h₂ v v₁ v₂ s l g))‖ ≤
        C * M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) := by
  obtain ⟨B, hB, hb⟩ := exists_frontSmoothedNonlinearity_bound (m := m) f D c φ ψ h₁ h₂ h₃ hR
  let A := B * (K * (7 * K + K ^ 2))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A + 1, by positivity, ?_⟩
  intro M t v v₁ v₂ σ s s₁ l g hM hM1 ht hv₁ hv₂ hsid hs₁ hlid hvR hv hs hl hg
  have hproduct := projected_nonlinearity_decay_product_le (norm_nonneg v) (norm_nonneg s)
    hK hM hM1 ht (by simpa only [div_eq_mul_inv, Real.rpow_neg_one] using hv) hl hs hg
  calc
    _ ≤ B * ‖v‖ * (‖v‖ + ‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖) :=
      hb v v₁ v₂ σ s s₁ l g hv₁ hv₂ hsid hs₁ hlid hvR
    _ ≤ B * ((K * (7 * K + K ^ 2)) * M ^ 2 *
        (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hproduct hB.le
    _ = A * M ^ 2 * (1 + t) ^ (-(3 : ℝ) / 2) * Real.log (2 + t) := by dsimp only [A]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by linarith))
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      exact mul_le_mul_of_nonneg_right (by linarith : A ≤ A + 1) (sq_nonneg M)

/-- Pass the smoothed-source estimate to time zero by continuity. The
initial datum itself need not possess either spatial derivative. -/
theorem frontSmoothedSource_decay_at_zero {T A : ℝ} (hT : 0 < T)
    (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)) (hN : ContinuousOn N (Icc 0 T))
    (hb : ∀ r ∈ Ioc 0 T,
      ‖heatFlowBUC (d_perp D φ ψ) (1 / 8) (longitudinalPairing ψ h₃.integrable (N r))‖ ≤
        A * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r)) :
    ∀ r ∈ Icc 0 T,
      ‖heatFlowBUC (d_perp D φ ψ) (1 / 8) (longitudinalPairing ψ h₃.integrable (N r))‖ ≤
        A * (1 + r) ^ (-(3 : ℝ) / 2) * Real.log (2 + r) := by
  apply le_on_Icc_of_le_on_Ioc hT _ _ hb
  · exact ((heatOperator (d_perp D φ ψ) (1 / 8)).continuous.comp_continuousOn
      ((longitudinalPairing ψ h₃.integrable).continuous.comp_continuousOn hN)).norm
  · simpa only [neg_div, mul_assoc] using
      (continuousOn_logarithmic_decay ((3 : ℝ) / 2) T).const_mul A

end

end Planarwave
