/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.FiniteHeatSystemRegularity
public import Planarwave.Analysis.HeatMildClassical

@[expose] public section

/-!
# Classical time differentiation of a coupled heat system

Differentiate the restarted coordinate mild equations and reconstruct the
vector time derivative. Commutation of the Laplacian with bounded linear
coordinates identifies the result with the original matrix diffusion.
-/

open Set
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

variable {E V ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]
  [Fintype ι]

omit [CompleteSpace V] [Fintype ι] in
/-- The actual coordinate time derivative, obtained from two spatial
derivatives and the mild equations on a positive-time interval. -/
theorem IsFiniteHeatSystemMildOn.coordinate_hasDerivAt
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {P : ι → V →L[ℝ] ℝ}
    {f : V → V} (hf : ContDiff ℝ ∞ f) {T δ : ℝ} {u : ℝ → BUC E V}
    (hm : IsFiniteHeatSystemMildOn a P f hf.continuous T u)
    (hu : Continuous u) (hδ : 0 ≤ δ) (hreg : BUCSpatialRegularOn (Icc δ T) 2 u)
    {t : ℝ} (ht : t ∈ Ioo δ T) (i : ι) (x : E) :
    HasDerivAt (fun r ↦ P i (u r x))
      (a i * P i (Δ (u t : E → V) x) + P i (f (u t x))) t := by
  let U := fun r ↦ BUC.postcompCLM (P i) (u r)
  let F := fun r ↦ BUC.postcompContinuous (fun v ↦ P i (f v))
    ((P i).continuous.comp hf.continuous) (u r)
  have hF : Continuous F :=
    (BUC.continuous_postcompContinuous (fun v ↦ P i (f v))
      (((P i).contDiff.comp hf).of_le (by simp))).comp hu
  have hU : BUCSpatialRegularOn (Icc δ T) 2 U := by
    apply (hreg.postcomp_smooth (P i) (P i).contDiff).congr
    intro r _
    exact BUC.ext fun _ ↦ rfl
  have hrestart : ∀ s ∈ Ico δ T, ∀ r ∈ Icc s T,
      U r = heatFlowBUC (a i) (r - s) (U s) +
        ∫ z in s..r, heatFlowBUC (a i) (r - z) (F z) := by
    intro s hs r hr
    have heq := hm s (r - s) (hδ.trans hs.1) (sub_nonneg.mpr hr.1)
      (by linarith [hr.2]) i
    have hsrc : (fun z ↦ BUC.postcompContinuous (fun v ↦ P i (f v))
        ((P i).continuous.comp hf.continuous) (u (s + z))) = fun z ↦ F (s + z) := rfl
    rw [add_sub_cancel, hsrc, heatDuhamel_shift] at heq
    exact heq
  have hd := hasDerivAt_heat_mild (ha i) hF hU hrestart ht x
  have hlap : Δ (U t : E → ℝ) x = P i (Δ (u t : E → V) x) :=
    (hreg.contDiff ⟨ht.1.le, ht.2.le⟩).contDiffAt.laplacian_CLM_comp_left (l := P i)
  simpa only [hlap, smul_eq_mul] using! hd

/-- Reconstructing the coordinate derivatives gives the original
matrix reaction--diffusion PDE pointwise, with a genuine time derivative. -/
theorem IsFiniteHeatSystemMildOn.hasDerivAt
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {P : ι → V →L[ℝ] ℝ}
    (Q : ι → ℝ →L[ℝ] V) (hPQ : ∀ v : V, ∑ i, Q i (P i v) = v)
    (D : V →L[ℝ] V) (hDP : ∀ i v, P i (D v) = a i * P i v)
    {f : V → V} (hf : ContDiff ℝ ∞ f) {T δ : ℝ} {u : ℝ → BUC E V}
    (hm : IsFiniteHeatSystemMildOn a P f hf.continuous T u)
    (hu : Continuous u) (hδ : 0 ≤ δ) (hreg : BUCSpatialRegularOn (Icc δ T) 2 u)
    {t : ℝ} (ht : t ∈ Ioo δ T) (x : E) :
    HasDerivAt (fun r ↦ u r x) (D (Δ (u t : E → V) x) + f (u t x)) t := by
  have hcoord (i : ι) := (Q i).hasFDerivAt.comp_hasDerivAt t
    (hm.coordinate_hasDerivAt ha hf hu hδ hreg ht i x)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hcoord i)
  have hval : (∑ i, Q i (a i * P i (Δ (u t : E → V) x) + P i (f (u t x)))) =
      D (Δ (u t : E → V) x) + f (u t x) := by
    simp_rw [← hDP, ← map_add]
    exact hPQ _
  simpa only [Function.comp_def, hPQ, hval] using hsum

end

end Planarwave
