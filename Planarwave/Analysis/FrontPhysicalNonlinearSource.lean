/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontNonlinearityContinuity
import all Planarwave.Analysis.FrontPhysicalModulationRegularity
import all Planarwave.Analysis.MatrixReactionDiffusionPositiveClosedJets

/-!
# Constructing the physical nonlinear source from rough initial data

Parabolic smoothing constructs the actual perturbation's spatial derivative
fields, continuous on `(0,T]`. The initial zero interval of the phase
coefficients removes these derivatives from the source near zero. Thus the
nonlinear source is continuous on the entire closed slab, without derivative
bounds on the initial datum. This does not impose a fixed-point equation for
the delayed forcing; causal self-consistency remains a separate step.
-/

open Set

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {d n : ℕ} [Nontrivial (ℝ^n)]
  (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) (hd : 2 ≤ d)

include h₃ in
/-- Genuine perturbation jets and its continuous nonlinear source are
constructed from the physical mild equation and the phase regularity.
No perturbation derivatives or nonlinear source path are supplied. -/
theorem exists_front_physical_nonlinear_source
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (u : ℝ → BUC (ℝ^d) (ℝ^n)) (hu : ContinuousOn u (Icc 0 T))
    (hm : IsMatrixReactionDiffusionMildOn f h₁.smooth.continuous D h₁.positive T u)
    (σ : ℝ → BUC (ℝ^(d - 1)) ℝ) (hσc : ContinuousOn σ (Icc 0 T))
    (hσreg : BUCSpatialRegularOn (Ioc 0 T) 2 σ)
    (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l g : ℝ → BUC (ℝ^(d - 1)) ℝ)
    (hs : ContinuousOn s (Ioc 0 T)) (hl : ContinuousOn l (Ioc 0 T))
    (hg : ContinuousOn g (Ioc 0 T))
    (hzero : ∀ t ∈ Icc 0 T, t < δ → s t = 0 ∧ l t = 0 ∧ g t = 0) :
    ∃ (v₁ : ℝ → BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
      (v₂ : ℝ → BUC (ℝ^(d - 1) × ℝ) ((ℝ^(d - 1) × ℝ) →L[ℝ] (ℝ^(d - 1) × ℝ) →L[ℝ] ℝ^n))
      (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)),
      ContinuousOn v₁ (Ioc 0 T) ∧ ContinuousOn v₂ (Ioc 0 T) ∧ ContinuousOn N (Icc 0 T) ∧
      (∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt
        (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)) (v₁ t x) x) ∧
      (∀ t ∈ Ioc 0 T, ∀ x, HasFDerivAt (v₁ t) (v₂ t x) x) ∧
      ∀ t, N t = frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
        (frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t))
        (v₁ t) (v₂ t) (s t) (l t) (g t) := by
  let v := fun t ↦ frontInverseModulatedPerturbation f D c φ h₂ hd (u t) (c * t) (σ t)
  have hvc : ContinuousOn v (Icc 0 T) :=
    continuousOn_frontInverseModulatedPerturbation f D c φ h₂ hd hu (by fun_prop) hσc
  have hvr : BUCSpatialRegularOn (Ioc 0 T) 2 v :=
    spatialRegularOn_frontInverseModulatedPerturbation f D c φ h₂ hd ψ h₁ h₃
      (hm.spatialRegularOn_Ioc h₁ hT hu 2) (by fun_prop) hσreg
  obtain ⟨_, v₁, hv₁, hd₁⟩ := hvr
  obtain ⟨hv₁c, v₂, hv₂c, hd₂⟩ := hv₁
  let N := fun t ↦ frontInverseModulationNonlinearity f D c φ ψ h₁ h₂
    (v t) (v₁ t) (v₂ t) (s t) (l t) (g t)
  have hN : ContinuousOn N (Icc 0 T) :=
    continuousOn_frontInverseModulationNonlinearity_of_initial_zero f D c φ ψ h₁ h₂ hδ
      hvc hv₁c hv₂c hs hl hg hzero
  exact ⟨v₁, v₂, N, hv₁c, hv₂c, hN, hd₁, hd₂, fun _ ↦ rfl⟩

end

end Planarwave
