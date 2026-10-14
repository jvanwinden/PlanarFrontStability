/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpacetimeRegularity
public import Planarwave.Analysis.BUCMixedDerivatives

@[expose] public section

/-!
# Bootstrapping all spatial jets in joint spacetime regularity

If the time derivative has jointly `C^k` spatial jets and the trajectory
has one more spatial derivative, the trajectory's jets are jointly
`C^(k+1)`. The mixed derivative identity is obtained from time integration
in the closed spatial derivative graph, not assumed.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance spacetimeBootstrapDerivativeNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance spacetimeBootstrapDerivativeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance spacetimeBootstrapBUCDerivativeNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] F)) := BUC.instNormedAddCommGroup
local instance spacetimeBootstrapBUCDerivativeNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] F)) := BUC.instNormedSpace

/-- Gain one joint derivative simultaneously for every spatial jet up to
order `j`, using genuine time differentiation and spatial commutation. -/
theorem BUCSpacetimeRegularOn.time_upgrade {a b : ℝ} {k j : ℕ}
    {u v : ℝ → BUC E F}
    (hu : BUCSpacetimeRegularOn a b k (j + 1) u)
    (hv : BUCSpacetimeRegularOn a b k j v)
    (htime : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t) :
    BUCSpacetimeRegularOn a b (k + 1) j u := by
  induction j generalizing F with
  | zero =>
    obtain ⟨hc, _, q, hq, hd⟩ := hu
    refine ⟨hc, ?_⟩
    exact contDiffOn_succ_spacetime isOpen_Ioo k hv.joint hq.joint htime
      (fun t ht ↦ hd t ⟨ht.1.le, ht.2.le⟩)
  | succ j ih =>
    have hvc := hv.continuous
    have hvjoint := hv.joint
    obtain ⟨hc, _, q, hq, hd⟩ := hu
    obtain ⟨_, _, qv, hqv, hdv⟩ := hv
    have hqt : ∀ t ∈ Ioo a b, ∀ x,
        HasDerivAt (fun r ↦ q r x) (qv t x) t := by
      intro t ht x
      have htq := hasDerivAt_buc_spatial_derivative hc hvc hqv.continuous htime hd hdv ht
      simpa only [Function.comp_def, BUC.evalCLM_apply] using!
        (BUC.evalCLM (𝕜 := ℝ) x).hasFDerivAt.comp_hasDerivAt t htq
    refine ⟨hc, ?_, q, ih hq hqv hqt, hd⟩
    exact contDiffOn_succ_spacetime isOpen_Ioo k hvjoint hq.joint htime
      (fun t ht ↦ hd t ⟨ht.1.le, ht.2.le⟩)

end

end Planarwave
