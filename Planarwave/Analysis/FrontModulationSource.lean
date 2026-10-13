/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontRealProfileDerivatives
import all Planarwave.Analysis.FrontTrackingDecay
import all Planarwave.Analysis.FrontDelayedForcing
import all Planarwave.Analysis.FrontForcedPhaseFirstDerivativeBounds
import all Planarwave.Analysis.FrontForcedPhaseSecondDerivativeBounds
import Planarwave.Analysis.ModulationSourceDecay

/-!
# The full modulation source for the original front

The BUC realization of `eq:defNtilde`, with the original front derivatives
and diffusivity. The source estimate in Step 3a now follows from the phase
gradient/Laplacian bounds and the supplied nonlinear source decay. Decay of
the actual delayed forcing is proved internally.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {m n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The profile multiplying the phase Laplacian. -/
def frontPhaseLaplacianProfile : BUC ℝ (ℝ^n) :=
  d_perp D φ ψ • realTranslationModeBUC f D c φ ψ h₃ -
    BUC.postcompCLM D (realTranslationModeBUC f D c φ ψ h₃)

/-- The profile multiplying the squared phase gradient. -/
def frontPhaseGradientProfile : BUC ℝ (ℝ^n) :=
  BUC.postcompCLM D (realTranslationModeDerivativeBUC f D c φ ψ h₃) +
    (c / 2) • realTranslationModeBUC f D c φ ψ h₃

/-- The complete perturbation source in `eq:defNtilde`. -/
def frontModulationSource (N : BUC (ℝ^m × ℝ) (ℝ^n))
    (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ) : BUC (ℝ^m × ℝ) (ℝ^n) :=
  modulationPerturbationSource (frontPhaseLaplacianProfile f D c φ ψ h₃)
    (frontPhaseGradientProfile f D c φ ψ h₃) (realTranslationModeBUC f D c φ ψ h₃) N s l g

/-- Exact identification with the four terms of the paper, including signs. -/
theorem frontModulationSource_apply (N : BUC (ℝ^m × ℝ) (ℝ^n))
    (s : BUC (ℝ^m) (ℝ^m)) (l g : BUC (ℝ^m) ℝ) (y : ℝ^m) (z : ℝ) :
    frontModulationSource f D c φ ψ h₃ N s l g (y, z) =
      l y • (d_perp D φ ψ • deriv φ z - D (deriv φ z)) +
      ‖s y‖ ^ 2 • (D (deriv (deriv φ) z) + (c / 2) • deriv φ z) +
      N (y, z) - g y • deriv φ z := by
  simp only [frontModulationSource, modulationPerturbationSource_apply,
    frontPhaseLaplacianProfile, frontPhaseGradientProfile, BUC.add_apply, BUC.sub_apply,
    BUC.smul_apply, BUC.postcompCLM_apply, realTranslationModeBUC_apply,
    realTranslationModeDerivativeBUC_apply]

theorem continuousOn_frontModulationSource {I : Set ℝ}
    {N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n)} {s : ℝ → BUC (ℝ^m) (ℝ^m)}
    {l g : ℝ → BUC (ℝ^m) ℝ} (hN : ContinuousOn N I) (hs : ContinuousOn s I)
    (hl : ContinuousOn l I) (hg : ContinuousOn g I) :
    ContinuousOn (fun t ↦ frontModulationSource f D c φ ψ h₃ (N t) (s t) (l t) (g t)) I :=
  continuousOn_modulationPerturbationSource _ _ _ hN hs hl hg

/-- A positive constant controlling the full source, including the actual
delayed forcing. It is chosen before the data, horizon, and paths. -/
def frontModulationSourceDecayConstant (K : ℝ) : ℝ :=
  modulationSourceDecayConstant (frontPhaseLaplacianProfile f D c φ ψ h₃)
    (frontPhaseGradientProfile f D c φ ψ h₃) (realTranslationModeBUC f D c φ ψ h₃)
    (max K (frontForcingC2DecayConstant D φ ψ (5 / 4)))

theorem frontModulationSourceDecayConstant_pos (K : ℝ) :
    0 < frontModulationSourceDecayConstant f D c φ ψ h₃ K :=
  modulationSourceDecayConstant_pos _ _ _
    ((frontForcingC2DecayConstant_pos D φ ψ (5 / 4)).le.trans (le_max_right _ _))

/-- The exact source bound `eq:Ntildeest`. No separate decay assumption
on the forcing, or any spatial derivative bound on `N`, is needed. -/
theorem norm_frontModulationSource_decay_le {K T M t : ℝ}
    (v₀ : BUC (ℝ^m × ℝ) (ℝ^n)) (N : ℝ → BUC (ℝ^m × ℝ) (ℝ^n))
    (s : BUC (ℝ^m) (ℝ^m)) (l : BUC (ℝ^m) ℝ)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (hv₀ : ‖v₀‖ ≤ M)
    (hN : ∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4))
    (ht : t ∈ Icc 0 T)
    (hs : ‖s‖ ≤ K * M * (1 + t) ^ (-(1 / 2 : ℝ)))
    (hl : ‖l‖ ≤ K * M * (1 + t) ^ (-(1 : ℝ))) :
    ‖frontModulationSource f D c φ ψ h₃ (N t) s l (frontDelayedForcing f D c φ ψ h₃ v₀ N t)‖ ≤
      frontModulationSourceDecayConstant f D c φ ψ h₃ K * M / (1 + t) := by
  have hK : 0 ≤ max K (frontForcingC2DecayConstant D φ ψ (5 / 4)) :=
    ((frontForcingC2DecayConstant_pos D φ ψ (5 / 4)).le.trans (le_max_right _ _))
  have hg : ‖frontDelayedForcing f D c φ ψ h₃ v₀ N t‖ ≤
      frontForcingC2DecayConstant D φ ψ (5 / 4) * M * (1 + t) ^ (-(5 : ℝ) / 4) := by
    apply (le_max_left _ _).trans
    simpa only [neg_div] using norm_frontDelayedForcing_c2_decay_le f D c φ ψ h₃
      (by norm_num : (0 : ℝ) ≤ 5 / 4) v₀ N hM hv₀ (by simpa only [neg_div] using hN) ht
  apply norm_modulationPerturbationSource_decay_le _ _ _ _ _ _ _ hK hM hM1 ht.1 (hN t ht)
  · apply hs.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
      (Real.rpow_nonneg (by linarith [ht.1]) _)
  · apply hl.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
      (Real.rpow_nonneg (by linarith [ht.1]) _)
  · apply hg.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
      (Real.rpow_nonneg (by linarith [ht.1]) _)

end

end Planarwave
