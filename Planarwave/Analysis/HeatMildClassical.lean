/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatDuhamelTimeRegularity
public import Planarwave.Analysis.BUCSpatialRegularity

@[expose] public section

/-!
# Classical time derivatives of spatially regular heat solutions

On a compact positive-time interval, two genuine spatial BUC derivatives
turn the restarted mild formula into the classical heat equation. The
Hessian need only be continuous on that interval; constant extension is
used for the right-derivative fundamental theorem of calculus.
-/

open Set
open scoped Laplacian

namespace Planarwave

noncomputable section

universe u

variable {E : Type} {F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance heatMildSecondTensorNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance heatMildSecondTensorNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- The classical BUC-valued time derivative, derived from the mild
formula and spatial regularity, rather than added to the solution data. -/
theorem exists_heat_mild_time_derivative {a δ T : ℝ} (ha : 0 < a) (hδT : δ ≤ T)
    {u f : ℝ → BUC E F} (hf : Continuous f)
    (hreg : BUCSpatialRegularOn (Icc δ T) 2 u)
    (hm : ∀ s ∈ Ico δ T, ∀ t ∈ Icc s T,
      u t = heatFlowBUC a (t - s) (u s) +
        ∫ r in s..t, heatFlowBUC a (t - r) (f r)) :
    ∃ v : ℝ → BUC E F, Continuous v ∧
      (∀ t ∈ Icc δ T, HasDerivWithinAt u (v t) (Icc δ T) t) ∧
      ∀ t ∈ Icc δ T, ∀ x, v t x = a • Δ (u t : E → F) x + f t x := by
  obtain ⟨hu, q, ⟨hq, h, hh, hd₂⟩, hd₁⟩ := hreg
  let H : C(Icc δ T, BUC E (E →L[ℝ] E →L[ℝ] F)) :=
    ⟨fun t ↦ h t, continuousOn_iff_continuous_domRestrict.mp hh⟩
  let hext : ℝ → BUC E (E →L[ℝ] E →L[ℝ] F) := fun t ↦ H (projIcc δ T hδT t)
  have hextc : Continuous hext := H.continuous.comp continuous_projIcc
  have hexteq (t : ℝ) (ht : t ∈ Icc δ T) : hext t = h t := by
    simp [hext, H, projIcc, ht.1, ht.2]
    rfl
  let L : BUC E (E →L[ℝ] E →L[ℝ] F) →L[ℝ] BUC E F :=
    BUC.postcompCLM (laplacianTraceCLM (E := E) (F := F))
  let v := fun t ↦ a • L (hext t) + f t
  have hvc : Continuous v := ((L.continuous.comp hextc).const_smul a).add hf
  have hgen (t : ℝ) (ht : t ∈ Icc δ T) :
      convectiveGeneratorBUC a 0 (q t) (h t) + f t = v t := by
    dsimp only [v]
    rw [hexteq t ht]
    congr 1
    ext x
    simp [convectiveGeneratorBUC, L]
  have hright : ∀ s ∈ Ico δ T, HasDerivWithinAt u (v s) (Ici s) s := by
    intro s hs
    rw [← hgen s ⟨hs.1, hs.2.le⟩]
    exact hasDerivWithinAt_heat_restart ha hs.2 hf (q s) (h s)
      (hd₁ s ⟨hs.1, hs.2.le⟩) (hd₂ s ⟨hs.1, hs.2.le⟩) (hm s hs)
  refine ⟨v, hvc, fun t ht ↦
    hasDerivWithinAt_of_continuous_right_derivative hu hvc hright ht, ?_⟩
  intro t ht x
  change a • laplacianTraceCLM (hext t x) + f t x = _
  rw [hexteq t ht, laplacian_eq_trace_of_hasFDerivAt (u t) (q t) (h t)
    (hd₁ t ht) (hd₂ t ht)]

/-- Pointwise heat equation at interior times, with its actual time
derivative obtained from the Banach-valued derivative. -/
theorem hasDerivAt_heat_mild {a δ T : ℝ} (ha : 0 < a)
    {u f : ℝ → BUC E F} (hf : Continuous f)
    (hreg : BUCSpatialRegularOn (Icc δ T) 2 u)
    (hm : ∀ s ∈ Ico δ T, ∀ t ∈ Icc s T,
      u t = heatFlowBUC a (t - s) (u s) +
        ∫ r in s..t, heatFlowBUC a (t - r) (f r))
    {t : ℝ} (ht : t ∈ Ioo δ T) (x : E) :
    HasDerivAt (fun r ↦ u r x) (a • Δ (u t : E → F) x + f t x) t := by
  obtain ⟨v, _, hd, heq⟩ := exists_heat_mild_time_derivative ha (ht.1.trans ht.2).le hf hreg hm
  have hdt := (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hp : HasDerivAt (fun r ↦ u r x) (v t x) t := by
    simpa only [Function.comp_def, BUC.evalCLM_apply] using!
      (BUC.evalCLM (𝕜 := ℝ) x).hasFDerivAt.comp_hasDerivAt t hdt
  rwa [heq t ⟨ht.1.le, ht.2.le⟩] at hp

end

end Planarwave
