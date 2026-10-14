/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpacetimeBootstrap
public import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional

@[expose] public section

/-!
# Full joint smoothness for reaction--diffusion solutions

The spatial smoothing estimates and the actual PDE imply joint smoothness
on positive-time slabs. At each step, the PDE supplies one additional
joint derivative while consuming two spatial derivatives. All spatial
jets are advanced together, so mixed derivatives are included.
-/

open Set
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

variable {E V : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance reactionSmoothGradientNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] V) := inferInstance
local instance reactionSmoothGradientNormedSpace :
    NormedSpace ℝ (E →L[ℝ] V) := inferInstance
local instance reactionSmoothHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance reactionSmoothHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance reactionSmoothBUCGradientNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] V)) := BUC.instNormedAddCommGroup
local instance reactionSmoothBUCGradientNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] V)) := BUC.instNormedSpace
local instance reactionSmoothBUCHessianNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] V)) := BUC.instNormedAddCommGroup
local instance reactionSmoothBUCHessianNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] V)) := BUC.instNormedSpace

set_option maxHeartbeats 1200000 in
/-- All spatial jets of a reaction--diffusion solution acquire every
finite joint spacetime order, starting from spatial BUC smoothing. -/
theorem bucSpacetimeRegularOn_reactionDiffusion
    {a b : ℝ} {u : ℝ → BUC E V}
    (hreg : ∀ j, BUCSpatialRegularOn (Icc a b) j u)
    (D : V →L[ℝ] V) (f : V → V) (hf : ContDiff ℝ ∞ f)
    (hpde : ∀ t ∈ Ioo a b, ∀ x,
      HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → V) x) + f (u t x)) t)
    (k j : ℕ) : BUCSpacetimeRegularOn a b k j u := by
  induction k generalizing j with
  | zero => exact BUCSpacetimeRegularOn.of_spatialRegular (hreg j)
  | succ k ih =>
    have hprev := ih (j + 2)
    have hstep := hprev.of_succ
    obtain ⟨_, _, q, ⟨_, _, H, hH, hd₂⟩, hd₁⟩ := hprev
    let L := D.comp (laplacianTraceCLM (E := E) (F := V))
    let v := fun t ↦ BUC.postcompCLM L (H t) + BUC.postcompContinuous f hf.continuous (u t)
    have hsource : BUCSpacetimeRegularOn a b k j v := by
      have hL : BUCSpacetimeRegularOn a b k j (fun t ↦ BUC.postcompCLM L (H t)) := by
        apply (hH.postcomp_smooth L L.contDiff).congr
        intro t _
        exact BUC.ext fun _ ↦ rfl
      exact hL.add ((ih j).postcomp_smooth f hf)
    apply hstep.time_upgrade hsource
    intro t ht x
    have hval : v t x = D (Δ (u t : E → V) x) + f (u t x) := by
      change D (laplacianTraceCLM (H t x)) + f (u t x) = _
      rw [laplacian_eq_trace_of_hasFDerivAt (u t) (q t) (H t)
        (hd₁ t ⟨ht.1.le, ht.2.le⟩) (hd₂ t ⟨ht.1.le, ht.2.le⟩)]
    rw [hval]
    exact hpde t ht x

/-- Spatial smoothing and the PDE imply joint `C∞`, not merely smooth
spatial slices. This is the local classical regularity used in the
paper's final proof before the bounded-norm continuation argument. -/
theorem BUCSpatialRegularOn.contDiffOn_infty_reactionDiffusion
    {a b : ℝ} {u : ℝ → BUC E V}
    (hreg : ∀ j, BUCSpatialRegularOn (Icc a b) j u)
    (D : V →L[ℝ] V) (f : V → V) (hf : ContDiff ℝ ∞ f)
    (hpde : ∀ t ∈ Ioo a b, ∀ x,
      HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → V) x) + f (u t x)) t) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ u p.1 p.2) (Ioo a b ×ˢ univ) := by
  apply contDiffOn_infty.mpr
  intro k
  exact (bucSpacetimeRegularOn_reactionDiffusion hreg D f hf hpde k 0).joint

end

end Planarwave
