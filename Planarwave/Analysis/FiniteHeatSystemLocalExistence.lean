/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.NonlinearVolterra
public import Planarwave.Analysis.FiniteHeatSystemRegularity

@[expose] public section

/-!
# Local existence for a coupled finite heat system

Reconstruct the real matrix heat evolution from scalar heat operators in
fixed coordinates. The nonlinear Volterra contraction gives actual mild
solutions, with lifespan and norm bounds uniform on a bounded set of
initial data. The reaction is allowed to couple all coordinates.
-/

open Set MeasureTheory
open scoped ContDiff

namespace Planarwave

noncomputable section

variable {E V ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]
  [Fintype ι] [DecidableEq ι]

/-- Real heat evolution, reconstructed in fixed diffusion coordinates. -/
def finiteHeatSystemOperator (a : ι → ℝ) (P : ι → V →L[ℝ] ℝ)
    (Q : ι → ℝ →L[ℝ] V) (t : ℝ) : BUC E V →L[ℝ] BUC E V :=
  ∑ i, (BUC.postcompCLM (Q i)).comp
    ((heatOperator (a i) t).comp (BUC.postcompCLM (P i)))

omit [ProperSpace V] [CompleteSpace V] [DecidableEq ι] in
theorem finiteHeatSystemOperator_apply (a : ι → ℝ) (P : ι → V →L[ℝ] ℝ)
    (Q : ι → ℝ →L[ℝ] V) (t : ℝ) (u : BUC E V) :
    finiteHeatSystemOperator a P Q t u =
      ∑ i, BUC.postcompCLM (Q i) (heatFlowBUC (a i) t (BUC.postcompCLM (P i) u)) := by
  simp only [finiteHeatSystemOperator, sum_apply,
    ContinuousLinearMap.comp_apply, heatOperator_apply]

omit [ProperSpace V] [CompleteSpace V] [DecidableEq ι] in
theorem continuous_finiteHeatSystemOperator_joint (a : ι → ℝ)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V) :
    Continuous (fun p : ℝ × BUC E V ↦ finiteHeatSystemOperator a P Q p.1 p.2) := by
  simp only [finiteHeatSystemOperator_apply]
  apply continuous_finsetSum
  intro i _
  exact (BUC.postcompCLM (Q i)).continuous.comp ((continuous_heatFlowBUC_joint (a i)).comp
    (continuous_fst.prodMk ((BUC.postcompCLM (P i)).continuous.comp continuous_snd)))

omit [ProperSpace V] [CompleteSpace V] [DecidableEq ι] in
theorem norm_finiteHeatSystemOperator_le (a : ι → ℝ) (P : ι → V →L[ℝ] ℝ)
    (Q : ι → ℝ →L[ℝ] V) (t : ℝ) :
    ‖finiteHeatSystemOperator (E := E) a P Q t‖ ≤ ∑ i, ‖Q i‖ * ‖P i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ ↦ by positivity)
  intro u
  rw [finiteHeatSystemOperator_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ‖Q i‖ * ‖heatFlowBUC (a i) t (BUC.postcompCLM (P i) u)‖ :=
      BUC.norm_postcompCLM_apply_le _ _
    _ ≤ ‖Q i‖ * (‖P i‖ * ‖u‖) := mul_le_mul_of_nonneg_left
      ((norm_heatFlowBUC_le _ _ _).trans (BUC.norm_postcompCLM_apply_le _ _)) (norm_nonneg _)
    _ = _ := by ring

omit [ProperSpace V] [CompleteSpace V] [DecidableEq ι] in
theorem finiteHeatSystemOperator_zero (a : ι → ℝ) (P : ι → V →L[ℝ] ℝ)
    (Q : ι → ℝ →L[ℝ] V) (hPQ : ∀ v : V, ∑ i, Q i (P i v) = v) :
    finiteHeatSystemOperator (E := E) a P Q 0 = ContinuousLinearMap.id ℝ (BUC E V) := by
  ext u y
  simp only [finiteHeatSystemOperator_apply, heatFlowBUC_zero, ContinuousLinearMap.id_apply]
  change (BUC.evalCLM (𝕜 := ℝ) y) (∑ i, BUC.postcompCLM (Q i) (BUC.postcompCLM (P i) u)) = _
  rw [map_sum]
  exact hPQ (u y)

omit [ProperSpace V] [CompleteSpace V] in
/-- Projection of the reconstructed heat evolution is the corresponding
scalar heat evolution; no equal-diffusion assumption is used. -/
theorem postcomp_finiteHeatSystemOperator (a : ι → ℝ) (P : ι → V →L[ℝ] ℝ)
    (Q : ι → ℝ →L[ℝ] V)
    (hQP : ∀ i j z, P i (Q j z) = if i = j then z else 0)
    (t : ℝ) (u : BUC E V) (i : ι) :
    BUC.postcompCLM (P i) (finiteHeatSystemOperator a P Q t u) =
      heatFlowBUC (a i) t (BUC.postcompCLM (P i) u) := by
  rw [finiteHeatSystemOperator_apply, map_sum]
  apply BUC.ext
  intro y
  change (BUC.evalCLM (𝕜 := ℝ) y) (∑ j, _) = _
  rw [map_sum]
  simp only [BUC.evalCLM_apply, BUC.postcompCLM_apply, hQP]
  simp

set_option maxHeartbeats 800000 in
/-- A single BUC-valued mild equation gives all scalar coordinate
equations and therefore all restart equations. -/
theorem isFiniteHeatSystemMildOn_of_operator_mild (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V)
    (hQP : ∀ i j z, P i (Q j z) = if i = j then z else 0)
    (f : V → V) (hf : ContDiff ℝ ∞ f) {T : ℝ} {u : ℝ → BUC E V}
    (hu : Continuous u)
    (hm : ∀ t ∈ Icc 0 T, u t = finiteHeatSystemOperator a P Q t (u 0) +
      ∫ r in 0..t, finiteHeatSystemOperator a P Q (t - r)
        (BUC.postcompContinuous f hf.continuous (u r))) :
    IsFiniteHeatSystemMildOn a P f hf.continuous T u := by
  apply isFiniteHeatSystemMildOn_of_mild a ha P f hf hu.continuousOn
  intro t ht i
  have hfc : Continuous (BUC.postcompContinuous (A := E) f hf.continuous) :=
    BUC.continuous_postcompContinuous f (hf.of_le (by simp))
  have hfu : Continuous (fun r ↦ BUC.postcompContinuous f hf.continuous (u r)) := hfc.comp hu
  have harg : Continuous (fun r : ℝ ↦ (t - r, BUC.postcompContinuous f hf.continuous (u r))) :=
    (continuous_const.sub continuous_id).prodMk hfu
  have hc : Continuous (fun r : ℝ ↦ finiteHeatSystemOperator a P Q (t - r)
      (BUC.postcompContinuous f hf.continuous (u r))) := by
    simpa only [Function.comp_def] using!
      (continuous_finiteHeatSystemOperator_joint (E := E) a P Q).comp harg
  rw [hm t ht, map_add,
    ← (BUC.postcompCLM (P i)).intervalIntegral_comp_comm (hc.intervalIntegrable _ _),
    postcomp_finiteHeatSystemOperator a P Q hQP]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  calc
    _ = heatFlowBUC (a i) (t - r)
        (BUC.postcompCLM (P i) (BUC.postcompContinuous f hf.continuous (u r))) := by
      simpa only using! postcomp_finiteHeatSystemOperator a P Q hQP (t - r)
        (BUC.postcompContinuous f hf.continuous (u r)) i
    _ = _ := congrArg (heatFlowBUC (a i) (t - r)) (BUC.ext fun _ ↦ rfl)

set_option maxHeartbeats 800000 in
/-- Uniform positive lifetime for the coupled nonlinear heat system,
with the initial datum attained in BUC norm and exact restart formulas. -/
theorem exists_local_finiteHeatSystem (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V)
    (hPQ : ∀ v : V, ∑ i, Q i (P i v) = v)
    (hQP : ∀ i j z, P i (Q j z) = if i = j then z else 0)
    (f : V → V) (hf : ContDiff ℝ ∞ f) {B : ℝ} (hB : 0 ≤ B) :
    ∃ T > 0, T ≤ 1 ∧ ∀ u₀ : BUC E V, ‖u₀‖ ≤ B → ∃ u : ℝ → BUC E V,
      Continuous u ∧ u 0 = u₀ ∧
        (∀ t, ‖u t‖ ≤ (∑ i, ‖Q i‖ * ‖P i‖) * B + 1) ∧
        IsFiniteHeatSystemMildOn a P f hf.continuous T u := by
  obtain ⟨T, hT, hT₁, hex⟩ := exists_local_nonlinearVolterra
    (finiteHeatSystemOperator (E := E) a P Q) (continuous_finiteHeatSystemOperator_joint (E := E) a P Q)
    (finiteHeatSystemOperator_zero (E := E) a P Q hPQ)
    (BUC.postcompContinuous f hf.continuous)
    (BUC.continuous_postcompContinuous f (hf.of_le (by simp)))
    (BUC.exists_postcompContinuous_norm_bound f hf.continuous)
    (BUC.exists_postcompContinuous_lipschitz_bound f (hf.of_le (by simp)))
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (norm_nonneg (Q i)) (norm_nonneg (P i))) hB
    (fun t _ ↦ norm_finiteHeatSystemOperator_le (E := E) a P Q t)
  refine ⟨T, hT, hT₁, fun u₀ hu₀ ↦ ?_⟩
  obtain ⟨u, hu, hinit, hb, hm⟩ := hex u₀ hu₀
  refine ⟨u, hu, hinit, hb, isFiniteHeatSystemMildOn_of_operator_mild a ha P Q hQP f hf hu ?_⟩
  simpa only [hinit] using hm

end

end Planarwave
