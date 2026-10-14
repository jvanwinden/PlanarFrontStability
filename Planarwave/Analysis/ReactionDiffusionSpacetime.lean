/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpacetimeCalculus
public import Planarwave.Analysis.BUCMixedDerivatives
public import Planarwave.Analysis.BUCNonlinearHigher
public import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional

@[expose] public section

/-!
# Joint regularity of reaction--diffusion trajectories

Two time-continuous spatial BUC derivatives make the reaction--diffusion
right-hand side continuous in the BUC norm. The pointwise PDE therefore
supplies jointly continuous time derivatives and yields joint `C¹`
regularity. Spatial smoothness alone is not used as a substitute for
joint spacetime regularity.

Four spatial derivative fields suffice for joint `C²`: the first two
mixed time--space derivatives are derived by integrating in the closed
spatial derivative graph, and the PDE then differentiates once more.
-/

open Set
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

variable {E V : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]

local instance reactionSpacetimeGradientNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] V) := inferInstance
local instance reactionSpacetimeGradientNormedSpace :
    NormedSpace ℝ (E →L[ℝ] V) := inferInstance
local instance reactionSpacetimeHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance reactionSpacetimeHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance reactionSpacetimeBUCGradientNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] V)) := BUC.instNormedAddCommGroup
local instance reactionSpacetimeBUCGradientNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] V)) := BUC.instNormedSpace
local instance reactionSpacetimeBUCHessianNormedAddCommGroup :
    NormedAddCommGroup (BUC E (E →L[ℝ] E →L[ℝ] V)) := BUC.instNormedAddCommGroup
local instance reactionSpacetimeBUCHessianNormedSpace :
    NormedSpace ℝ (BUC E (E →L[ℝ] E →L[ℝ] V)) := BUC.instNormedSpace

/-- Joint `C¹` regularity from the genuine PDE and two continuous spatial
BUC derivative fields, without any prior joint differentiability assumption. -/
theorem BUCSpatialRegularOn.contDiffOn_one_reactionDiffusion
    {s : Set ℝ} (hs : IsOpen s) {u : ℝ → BUC E V}
    (hreg : BUCSpatialRegularOn s 2 u) (D : V →L[ℝ] V)
    (f : V → V) (hf : ContDiff ℝ 1 f)
    (hpde : ∀ t ∈ s, ∀ x,
      HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → V) x) + f (u t x)) t) :
    ContDiffOn ℝ 1 (fun p : ℝ × E ↦ u p.1 p.2) (s ×ˢ univ) := by
  obtain ⟨hu, q, ⟨hq, H, hH, hd₂⟩, hd₁⟩ := hreg
  let L : BUC E (E →L[ℝ] E →L[ℝ] V) →L[ℝ] BUC E V :=
    BUC.postcompCLM (D.comp (laplacianTraceCLM (E := E) (F := V)))
  let v := fun t ↦ L (H t) + BUC.postcompContinuous f hf.continuous (u t)
  have hvc : ContinuousOn v s := (L.continuous.comp_continuousOn hH).add
    ((BUC.continuous_postcompContinuous f hf).comp_continuousOn hu)
  have hval (t : ℝ) (ht : t ∈ s) (x : E) :
      v t x = D (Δ (u t : E → V) x) + f (u t x) := by
    change D (laplacianTraceCLM (H t x)) + f (u t x) = _
    rw [laplacian_eq_trace_of_hasFDerivAt (u t) (q t) (H t) (hd₁ t ht) (hd₂ t ht)]
  apply contDiffOn_one_buc_spacetime hs hvc hq _ hd₁
  intro t ht x
  rw [hval t ht x]
  exact hpde t ht x

set_option maxHeartbeats 1200000 in
/-- The second joint derivative follows from four spatial BUC
derivatives. Both mixed derivative identities are proved by time
integration; neither is postulated as additional solution data. -/
theorem BUCSpatialRegularOn.contDiffOn_two_reactionDiffusion
    [FiniteDimensional ℝ V] {a b : ℝ} {u : ℝ → BUC E V}
    (hreg : BUCSpatialRegularOn (Icc a b) 4 u) (D : V →L[ℝ] V)
    (f : V → V) (hf : ContDiff ℝ ∞ f)
    (hpde : ∀ t ∈ Ioo a b, ∀ x,
      HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → V) x) + f (u t x)) t) :
    ContDiffOn ℝ 2 (fun p : ℝ × E ↦ u p.1 p.2) (Ioo a b ×ˢ univ) := by
  have hreg₂ : BUCSpatialRegularOn (Icc a b) 2 u := hreg.of_le (by norm_num)
  obtain ⟨hu, q, ⟨hq, H, hHreg, hd₂⟩, hd₁⟩ := hreg
  let L := D.comp (laplacianTraceCLM (E := E) (F := V))
  let v := fun t ↦ BUC.postcompCLM L (H t) + BUC.postcompContinuous f hf.continuous (u t)
  have hsource : BUCSpatialRegularOn (Icc a b) 2 v := by
    have hL : BUCSpatialRegularOn (Icc a b) 2 (fun t ↦ BUC.postcompCLM L (H t)) := by
      apply (hHreg.postcomp_smooth L L.contDiff).congr
      intro t _
      exact BUC.ext fun _ ↦ rfl
    exact hL.add (hreg₂.postcomp_smooth f hf)
  have hval (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
      v t x = D (Δ (u t : E → V) x) + f (u t x) := by
    change D (laplacianTraceCLM (H t x)) + f (u t x) = _
    rw [laplacian_eq_trace_of_hasFDerivAt (u t) (q t) (H t) (hd₁ t ht) (hd₂ t ht)]
  have htime : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ u r x) (v t x) t := by
    intro t ht x
    rw [hval t ⟨ht.1.le, ht.2.le⟩ x]
    exact hpde t ht x
  obtain ⟨hv, qv, ⟨hqv, Hv, hHv, hdv₂⟩, hdv₁⟩ := hsource
  have hqt : ∀ t ∈ Ioo a b, HasDerivAt q (qv t) t := fun t ht ↦
    hasDerivAt_buc_spatial_derivative hu hv hqv htime hd₁ hdv₁ ht
  have hqtpoint : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ q r x) (qv t x) t := by
    intro t ht x
    simpa only [Function.comp_def, BUC.evalCLM_apply] using!
      (BUC.evalCLM (𝕜 := ℝ) x).hasFDerivAt.comp_hasDerivAt t (hqt t ht)
  have hHt : ∀ t ∈ Ioo a b, HasDerivAt H (Hv t) t := fun t ht ↦
    hasDerivAt_buc_spatial_derivative hq hqv hHv hqtpoint hd₂ hdv₂ ht
  have hHtpoint : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ H r x) (Hv t x) t := by
    intro t ht x
    simpa only [Function.comp_def, BUC.evalCLM_apply] using!
      (BUC.evalCLM (𝕜 := ℝ) x).hasFDerivAt.comp_hasDerivAt t (hHt t ht)
  obtain ⟨hH, K, hK, hd₃⟩ := hHreg
  have hujoint : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ u p.1 p.2) (Ioo a b ×ˢ univ) :=
    contDiffOn_one_buc_spacetime isOpen_Ioo (hv.mono Ioo_subset_Icc_self)
      (hq.mono Ioo_subset_Icc_self) htime (fun t ht ↦ hd₁ t ⟨ht.1.le, ht.2.le⟩)
  have hqjoint : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ q p.1 p.2) (Ioo a b ×ˢ univ) :=
    contDiffOn_one_buc_spacetime isOpen_Ioo (hqv.mono Ioo_subset_Icc_self)
      (hH.mono Ioo_subset_Icc_self) hqtpoint (fun t ht ↦ hd₂ t ⟨ht.1.le, ht.2.le⟩)
  have hHjoint : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ H p.1 p.2) (Ioo a b ×ˢ univ) :=
    contDiffOn_one_buc_spacetime isOpen_Ioo (hHv.mono Ioo_subset_Icc_self)
      (hK.continuous.mono Ioo_subset_Icc_self) hHtpoint (fun t ht ↦ hd₃ t ⟨ht.1.le, ht.2.le⟩)
  have hvjoint : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ v p.1 p.2) (Ioo a b ×ˢ univ) :=
    (L.contDiff.comp_contDiffOn hHjoint).add ((hf.of_le (by simp)).comp_contDiffOn hujoint)
  have hsucc := contDiffOn_succ_spacetime (s := Ioo a b)
    (u := fun t x ↦ u t x) (v := fun t x ↦ v t x) (q := fun t x ↦ q t x) isOpen_Ioo 1
    (by simpa only [Nat.cast_one] using! hvjoint)
    (by simpa only [Nat.cast_one] using! hqjoint) htime
    (fun t ht ↦ hd₁ t ⟨ht.1.le, ht.2.le⟩)
  simpa using! hsucc

end

end Planarwave
