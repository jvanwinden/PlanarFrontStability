/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupParameterAnalytic

@[expose] public section

/-!
# Joint strong continuity in time and bounded perturbation

The parameter-dependent Volterra solution is continuous in the uniform path norm.
Evaluation gives joint continuity in coefficient, time, and initial datum, even
at time zero. No operator-norm continuity in time is asserted.
-/

open Set Filter Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Joint continuity of the finite-horizon perturbed path and its initial datum. -/
theorem continuous_perturbedPath_joint (S : C0Semigroup ℂ E) (T : NNReal) :
    Continuous (fun p : (E →L[ℂ] E) × E ↦ S.perturbedPathOperator p.1 T p.2) := by
  change Continuous (fun p : (E →L[ℂ] E) × E ↦
    S.volterraInverse p.1 T (S.freePathOperator T p.2))
  exact ((S.contDiff_volterraInverse_coefficient T).continuous.comp continuous_fst).clm_apply
    ((S.freePathOperator T).continuous.comp continuous_snd)

/-- The clamped finite-horizon solution is jointly continuous in all three inputs. -/
theorem continuous_extend_perturbedPath_joint (S : C0Semigroup ℂ E) (T : NNReal) :
    Continuous (fun p : (E →L[ℂ] E) × ℝ × E ↦
      extendTimePath (S.perturbedPathOperator p.1 T p.2.2) p.2.1) := by
  have hp : Continuous (projIcc 0 (T : ℝ) T.2) := continuous_projIcc
  exact continuous_eval.comp
    (((S.continuous_perturbedPath_joint T).comp
      (continuous_fst.prodMk continuous_snd.snd)).prodMk
        (hp.comp continuous_snd.fst))

/-- Joint strong continuity of bounded perturbation, including the zero-time endpoint. -/
theorem continuous_boundedPerturbation_realOrbit_joint (S : C0Semigroup ℂ E) :
    Continuous (fun p : (E →L[ℂ] E) × ℝ × E ↦
      (S.boundedPerturbation p.1).realOrbit p.2.2 p.2.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨B, r, v⟩
  let T : NNReal := r.toNNReal + 1
  have hc := (S.continuous_extend_perturbedPath_joint T).comp
    (continuous_fst.prodMk
      ((NNReal.continuous_coe.comp (continuous_real_toNNReal.comp continuous_snd.fst)).prodMk continuous_snd.snd))
  apply hc.continuousAt.congr_of_eventuallyEq
  have hr : r < (T : ℝ) := by
    have h := Real.le_coe_toNNReal r
    change r < (r.toNNReal : ℝ) + 1
    linarith
  filter_upwards [(continuous_snd.fst.continuousAt : ContinuousAt
    (fun p : (E →L[ℂ] E) × ℝ × E ↦ p.2.1) (B, r, v)).eventually (gt_mem_nhds hr)] with p hp
  have ht : p.2.1.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hp.le
  change S.perturbedOperator p.1 p.2.1.toNNReal p.2.2 =
    extendTimePath (S.perturbedPathOperator p.1 T p.2.2) (p.2.1.toNNReal : ℝ)
  rw [S.perturbedOperator_eq_path p.1 ht]
  exact (extendTimePath_coe _ ⟨p.2.1.toNNReal, p.2.1.toNNReal.2, ht⟩).symm

end

end C0Semigroup
