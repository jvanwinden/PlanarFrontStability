/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.InverseModulationCoordinates
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Continuity of the inverse-modulation coordinates

The modulation pullback depends continuously on the translation, phase, and
BUC data, in the spatial supremum norm. Uniform continuity of the fixed data
is sufficient; no spatial differentiability is needed. This includes the
initial time for the rough BUC initial perturbations in the paper.
-/

namespace Planarwave

noncomputable section

variable {Y F : Type*} [NormedAddCommGroup Y] [NormedAddCommGroup F]

/-- Changes in the shear parameters displace every spatial point by at most
the sum of the translation distance and the phase supremum distance. -/
theorem dist_modulationCoordinates_le (a b : ℝ) (σ τ : BUC Y ℝ) (x : Y × ℝ) :
    dist (modulationCoordinates a σ x) (modulationCoordinates b τ x) ≤
      dist a b + dist σ τ := by
  simp only [modulationCoordinates, dist_prod_same_left]
  calc
    dist (x.2 + a + σ x.1) (x.2 + b + τ x.1) ≤
        dist (x.2 + a) (x.2 + b) + dist (σ x.1) (τ x.1) :=
      dist_add_add_le _ _ _ _
    _ ≤ dist a b + dist σ τ := by
      simpa only [dist_add_left] using
        add_le_add (le_refl (dist (x.2 + a) (x.2 + b))) (BUC.dist_apply_le σ τ x.1)

/-- Pullback by one shear is an isometry on BUC data. -/
theorem dist_modulationShift (a : ℝ) (σ : BUC Y ℝ) (u v : BUC (Y × ℝ) F) :
    dist (modulationShift a σ u) (modulationShift a σ v) = dist u v := by
  rw [dist_eq_norm, ← modulationShift_sub, norm_modulationShift, dist_eq_norm]

/-- For fixed BUC data, the modulation pullback is uniformly continuous in
both shear parameters, without a bounded-derivative hypothesis. -/
theorem uniformContinuous_modulationShift_parameters (u : BUC (Y × ℝ) F) :
    UniformContinuous (fun p : ℝ × BUC Y ℝ ↦ modulationShift p.1 p.2 u) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp u.uniformContinuous
    (ε / 2) (by linarith)
  refine ⟨δ / 3, by linarith, ?_⟩
  intro p q hpq
  have hp : dist p.1 q.1 < δ / 3 := (le_max_left _ _).trans_lt hpq
  have hq : dist p.2 q.2 < δ / 3 := (le_max_right _ _).trans_lt hpq
  have hbound : ‖modulationShift p.1 p.2 u - modulationShift q.1 q.2 u‖ ≤ ε / 2 := by
    apply (BUC.norm_le (by linarith)).mpr
    intro x
    change ‖u (modulationCoordinates p.1 p.2 x) -
      u (modulationCoordinates q.1 q.2 x)‖ ≤ ε / 2
    rw [← dist_eq_norm]
    exact (hmod ((dist_modulationCoordinates_le _ _ _ _ x).trans_lt
      (by linarith))).le
  rw [dist_eq_norm]
  exact hbound.trans_lt (by linarith)

/-- Joint continuity of the modulation pullback in translation, phase, and
BUC data. In particular, the data need not be spatially differentiable. -/
theorem continuous_modulationShift_joint :
    Continuous (fun p : (ℝ × BUC Y ℝ) × BUC (Y × ℝ) F ↦
      modulationShift p.1.1 p.1.2 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp
    (uniformContinuous_modulationShift_parameters p.2).continuous.continuousAt
    (ε / 2) (by linarith)
  refine ⟨min δ (ε / 2), lt_min hδ (by linarith), ?_⟩
  intro q hqp
  have hpar : dist q.1 p.1 < δ :=
    (le_max_left _ _).trans_lt (hqp.trans_le (min_le_left _ _))
  have hdata : dist q.2 p.2 < ε / 2 :=
    (le_max_right _ _).trans_lt (hqp.trans_le (min_le_right _ _))
  calc
    dist (modulationShift q.1.1 q.1.2 q.2) (modulationShift p.1.1 p.1.2 p.2) ≤
        dist (modulationShift q.1.1 q.1.2 q.2) (modulationShift q.1.1 q.1.2 p.2) +
          dist (modulationShift q.1.1 q.1.2 p.2) (modulationShift p.1.1 p.1.2 p.2) :=
      dist_triangle _ _ _
    _ < ε := by rw [dist_modulationShift]; linarith [hmod hpar]

/-- A continuous BUC trajectory remains continuous under continuously moving
modulation coordinates, including any initial endpoint in the time set. -/
theorem continuousOn_modulationShift {T : Type*} [TopologicalSpace T]
    {s : Set T} {a : T → ℝ} {σ : T → BUC Y ℝ} {u : T → BUC (Y × ℝ) F}
    (ha : ContinuousOn a s) (hσ : ContinuousOn σ s) (hu : ContinuousOn u s) :
    ContinuousOn (fun t ↦ modulationShift (a t) (σ t) (u t)) s :=
  continuous_modulationShift_joint.comp_continuousOn ((ha.prodMk hσ).prodMk hu)

end

end Planarwave
