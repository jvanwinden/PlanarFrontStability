/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontModulationSource
import all Planarwave.Analysis.FrontDelayedForcing
import all Planarwave.Analysis.RealSpatialEmbedding
import all Planarwave.Analysis.FrontSpatialRemainderDuhamelDecay
import all Planarwave.Analysis.FrontFourierDecomposition

/-!
# Step 3a for the actual tracking source

Insert the four-term source `eq:defNtilde` into the spatial semigroup's
Duhamel remainder. Its source estimate now follows from the phase and
nonlinearity estimates, not from an additional hypothesis on the full source.
The result is `eq:west`, including the initial term and time zero.
-/

open Set MeasureTheory

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n d : ℕ}

local instance trackingRemainderLongNormedAddCommGroup : NormedAddCommGroup (BUC ℝ (ℂ^n)) := inferInstance
local instance trackingRemainderLongRealNormedSpace : NormedSpace ℝ (BUC ℝ (ℂ^n)) := inferInstance
local instance trackingRemainderLongComplexNormedSpace : NormedSpace ℂ (BUC ℝ (ℂ^n)) := inferInstance
local instance trackingRemainderSliceNormedAddCommGroup : NormedAddCommGroup (BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n))) := inferInstance
local instance trackingRemainderSliceRealNormedSpace : NormedSpace ℝ (BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n))) := inferInstance
local instance trackingRemainderSliceComplexNormedSpace : NormedSpace ℂ (BUC (ℝ^(d-1)) (BUC ℝ (ℂ^n))) := inferInstance
local instance trackingRemainderFullNormedAddCommGroup : NormedAddCommGroup (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance trackingRemainderFullRealNormedSpace : NormedSpace ℝ (BUC (ℝ^d) (ℂ^n)) := inferInstance
local instance trackingRemainderFullComplexNormedSpace : NormedSpace ℂ (BUC (ℝ^d) (ℂ^n)) := inferInstance

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  [Nontrivial (ℝ^n)] (ψ : ℝ → ℝ^n) (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The source used in the spatial Duhamel formula, with the actual
delayed forcing and the original profile coefficients. -/
def frontTrackingSpatialSource (hd : 2 ≤ d) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ) (t : ℝ) :
    BUC (ℝ^d) (ℂ^n) :=
  embedSplitSpatial hd (frontModulationSource f D c φ ψ h₃ (N t) (s t) (l t)
    (frontDelayedForcing f D c φ ψ h₃ v₀ N t))

omit [Nontrivial (ℝ^n)] in
theorem continuousOn_frontTrackingSpatialSource (hd : 2 ≤ d)
    (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) {I : Set ℝ}
    {N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)}
    {s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))} {l : ℝ → BUC (ℝ^(d - 1)) ℝ}
    (hN : ContinuousOn N I) (hs : ContinuousOn s I) (hl : ContinuousOn l I) :
    ContinuousOn (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) I :=
  (embedSplitSpatial hd).continuous.comp_continuousOn
    (continuousOn_frontModulationSource f D c φ ψ h₃ hN hs hl
      (continuous_frontDelayedForcing f D c φ ψ h₃ v₀ N).continuousOn)

/-- The actual spatial-semigroup remainder associated with the tracking source. -/
def frontTrackingRemainder (hd : 2 ≤ d) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ) (t : ℝ) :
    BUC (ℝ^(d - 1)) (BUC ℝ (ℂ^n)) :=
  frontSpatialRemainderDuhamel f D c φ h₁ h₂ ψ h₃ hd (embedSplitSpatial hd v₀)
    (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) t

/-- Step 3a: the source and phase bounds imply the logarithmic remainder
estimate for the actual front semigroup. No bound on `Ntilde` is assumed. -/
theorem exists_frontTrackingRemainder_decay (hd : 2 ≤ d) (K : ℝ) :
    ∃ C > 0, ∀ (T M : ℝ) (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
      (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
      (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ),
      0 ≤ M → M ≤ 1 → ‖v₀‖ ≤ M →
      (∀ r ∈ Icc 0 T, ‖N r‖ ≤ M * (1 + r) ^ (-(5 : ℝ) / 4)) →
      (∀ r ∈ Icc 0 T, ‖s r‖ ≤ K * M * (1 + r) ^ (-(1 / 2 : ℝ))) →
      (∀ r ∈ Icc 0 T, ‖l r‖ ≤ K * M * (1 + r) ^ (-(1 : ℝ))) →
      ∀ t ∈ Icc 0 T, ‖frontTrackingRemainder f D c φ h₁ h₂ ψ h₃ hd v₀ N s l t‖ ≤
        (C * M / (1 + t)) * Real.log (2 + t) := by
  obtain ⟨C, hC, hb⟩ := exists_frontSpatialRemainderDuhamel_decay f D c φ h₁ h₂ ψ h₃ hd
  let A := frontModulationSourceDecayConstant f D c φ ψ h₃ K
  have hA : 0 < A := frontModulationSourceDecayConstant_pos f D c φ ψ h₃ K
  refine ⟨C * (A + 1), by positivity, ?_⟩
  intro T M v₀ N s l hM hM1 hv₀ hN hs hl t ht
  have hM' : M ≤ (A + 1) * M := by nlinarith
  have hi : ‖embedSplitSpatial hd v₀‖ ≤ (A + 1) * M := by
    rw [norm_embedSplitSpatial]
    exact hv₀.trans hM'
  have hsource : ∀ r ∈ Icc 0 T, ‖frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l r‖ ≤
      ((A + 1) * M) / (1 + r) := by
    intro r hr
    rw [frontTrackingSpatialSource, norm_embedSplitSpatial]
    apply (norm_frontModulationSource_decay_le f D c φ ψ h₃ v₀ N (s r) (l r)
      hM hM1 hv₀ hN hr (hs r hr) (hl r hr)).trans
    apply div_le_div_of_nonneg_right _ (by linarith [hr.1])
    exact mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith : A ≤ A + 1) hM
  have h := hb T ((A + 1) * M) (embedSplitSpatial hd v₀)
    (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) (by positivity) hi hsource t ht
  simpa only [frontTrackingRemainder, mul_assoc] using! h

/-- The tracking remainder occurs in the exact spatial Duhamel
decomposition. Time-continuity of the three supplied paths justifies
the integrals; the delayed forcing is already continuous. -/
theorem frontTrackingSpatialDuhamel_decomposition (hd : 2 ≤ d)
    (v₀ : BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (N : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n))
    (s : ℝ → BUC (ℝ^(d - 1)) (ℝ^(d - 1))) (l : ℝ → BUC (ℝ^(d - 1)) ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hN : ContinuousOn N (Icc 0 t))
    (hs : ContinuousOn s (Icc 0 t)) (hl : ContinuousOn l (Icc 0 t)) :
    spatialSlices hd ((frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit (embedSplitSpatial hd v₀) t +
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel
        (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) t) =
      (frontCriticalHeatEvolution f D c φ ψ h₃ t.toNNReal (spatialSlices hd (embedSplitSpatial hd v₀)) +
        ∫ r in (0 : ℝ)..t, frontCriticalHeatEvolution f D c φ ψ h₃ (t - r).toNNReal
          (spatialSlices hd (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l r))) +
      frontTrackingRemainder f D c φ h₁ h₂ ψ h₃ hd v₀ N s l t :=
  frontSpatialDuhamel_decomposition f D c φ h₁ h₂ ψ h₃ hd (embedSplitSpatial hd v₀)
    (frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ N s l) ht
    (continuousOn_frontTrackingSpatialSource f D c φ ψ h₃ hd v₀ hN hs hl)

end

end Planarwave
