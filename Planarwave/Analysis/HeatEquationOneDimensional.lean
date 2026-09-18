/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatJointSmoothReal
public import Planarwave.Analysis.HeatIsometry

@[expose] public section

/-!
# Classical heat flow in one-dimensional Euclidean spaces

Transfer the real-line results along an isometric coordinate equivalence. This permits using
them with the challenge's transverse space when the ambient spatial dimension is two.
-/

open Function Set
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Joint heat regularity transported from the real line to an isometric copy. -/
theorem contDiffOn_heatFlow_of_real_equiv (e : E ≃ₗᵢ[ℝ] ℝ) {a : ℝ} (ha : 0 < a)
    (f : BUC E F) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => heatFlow a p.1 f p.2) (Ioi 0 ×ˢ univ) := by
  let v := f.comp e.symm e.symm.isometry.uniformContinuous
  have hcoe : (v : ℝ → F) ∘ e = f := by funext x; simp [v]
  have heq (t : ℝ) : heatFlow a t f = heatFlow a t v ∘ e := by
    rw [← heatFlow_comp_linearIsometryEquiv e a t v v.continuous, hcoe]
  have hpair : ContDiff ℝ ∞ (fun p : ℝ × E => (p.1, e p.2)) :=
    contDiff_fst.prodMk (e.toContinuousLinearEquiv.contDiff.comp contDiff_snd)
  have hmap : MapsTo (fun p : ℝ × E => (p.1, e p.2)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have h := (contDiffOn_infty_heatFlow_uncurry_real ha v).comp hpair.contDiffOn hmap
  simpa only [comp_def, heq] using h

/-- The classical heat equation transported to an isometric copy of the real line. -/
theorem hasDerivAt_heatFlow_time_of_real_equiv (e : E ≃ₗᵢ[ℝ] ℝ) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) (f : BUC E F) (x : E) :
    HasDerivAt (fun r => heatFlow a r f x) (a • Δ (heatFlow a t f) x) t := by
  let v := f.comp e.symm e.symm.isometry.uniformContinuous
  have hcoe : (v : ℝ → F) ∘ e = f := by funext y; simp [v]
  have heq (r : ℝ) : heatFlow a r f = heatFlow a r v ∘ e := by
    rw [← heatFlow_comp_linearIsometryEquiv e a r v v.continuous, hcoe]
  simp_rw [heq]
  rw [laplacian_comp_linearIsometryEquiv e _ (contDiff_two_heatFlow_real ha ht v), comp_apply,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one]
  exact hasDerivAt_heatFlow_time_real ha ht v (e x)

end

end Planarwave
