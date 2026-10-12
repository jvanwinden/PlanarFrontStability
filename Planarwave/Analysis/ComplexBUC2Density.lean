/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.ComplexBUC2
public import Planarwave.Analysis.HeatJointSmoothReal

@[expose] public section

/-!
# Density of the longitudinal domain

Positive-time heat regularization supplies two bounded uniformly continuous derivatives.
Strong continuity at time zero then proves that the common `BUC²` domain is dense in `BUC`.
This is the density required for the longitudinal generators in Section 2 of the paper.
-/

open Filter Set Topology

namespace Planarwave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [SMulCommClass ℝ ℂ F] [CompleteSpace F]

/-- Heat regularization at positive time belongs to the common longitudinal graph domain. -/
theorem exists_complexBUC2_heatFlowBUC {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : BUC ℝ F) : ∃ v : ComplexBUC2 F, ComplexBUC2.value F v = heatFlowBUC a t f := by
  obtain ⟨g, h, hg, hh⟩ := exists_buc_derivatives_heatFlow_real ha ht f
  exact ⟨⟨((heatFlowBUC a t f, g), h), fun x ↦ ⟨hg x, hh x⟩⟩, rfl⟩

/-- The longitudinal `BUC²` domain is dense in `BUC` in the supremum norm. -/
theorem denseRange_complexBUC2_value : DenseRange (ComplexBUC2.value F) := by
  intro f
  have hlim : Tendsto (fun t : ℝ ↦ heatFlowBUC 1 t f) (𝓝[>] 0) (𝓝 f) := by
    simpa only [heatFlowBUC_zero] using
      (continuous_heatFlowBUC_time 1 f).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact subset_closure (exists_complexBUC2_heatFlowBUC zero_lt_one ht f)

/-- Dense-domain statement in the continuous-linear-map interface. -/
theorem denseRange_complexBUC2_valueCLM : DenseRange (ComplexBUC2.valueCLM F) :=
  denseRange_complexBUC2_value

end Planarwave
