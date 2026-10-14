/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.CompatibleLocalTrajectories
public import Planarwave.Analysis.FiniteHeatSystemBoundedContinuation
public import Planarwave.Analysis.EndpointNormBound

@[expose] public section

/-!
# Maximal solutions of coupled finite heat systems

Uniqueness identifies all local trajectories with a common initial datum.
Their compatible union is defined up to the supremum of the existence
times. Every compact-time solution extends locally. Consequently, a finite
maximal time can only occur when the BUC norm has infinite endpoint limsup.
-/

open Set Filter
open scoped ContDiff Topology ENNReal

namespace Planarwave

noncomputable section

variable {E V ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [CompleteSpace V]
  [Fintype ι] [DecidableEq ι]

/-- The original coupled mild equations satisfy all hypotheses for the
compatible-union construction, without bounds on the initial datum. -/
theorem finiteHeatSystem_localTrajectorySystem
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V)
    (hPQ : ∀ z : V, ∑ i, Q i (P i z) = z)
    (hQP : ∀ i j z, P i (Q j z) = if i = j then z else 0)
    (f : V → V) (hf : ContDiff ℝ ∞ f) (u₀ : BUC E V) :
    LocalTrajectorySystem (IsFiniteHeatSystemMildOn a P f hf.continuous) u₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨T, hT, _, hex⟩ := exists_local_finiteHeatSystem (E := E)
      a ha P Q hPQ hQP f hf (norm_nonneg u₀)
    obtain ⟨u, hu, hinit, _, hm⟩ := hex u₀ le_rfl
    exact ⟨T, hT, u, hT.le, hu.continuousOn, hinit, hm⟩
  · intro S T u _ hST hm
    exact hm.mono hST
  · intro T u v heq hm
    exact hm.congr heq
  · intro S T u v hu hv
    apply IsFiniteHeatSystemMildOn.eqOn hf (le_min hu.nonneg hv.nonneg)
      (hu.equation.mono (min_le_left S T)) (hv.equation.mono (min_le_right S T)) Q hPQ
    · exact hu.continuous.mono (Icc_subset_Icc le_rfl (min_le_left _ _))
    · exact hv.continuous.mono (Icc_subset_Icc le_rfl (min_le_right _ _))
    · exact hu.initial.trans hv.initial.symm
  · intro T u hu
    obtain ⟨τ, hτ, _, hex⟩ := exists_local_finiteHeatSystem (E := E)
      a ha P Q hPQ hQP f hf (norm_nonneg (u T))
    obtain ⟨v, hv, hinit, _, hmv⟩ := hex (u T) le_rfl
    refine ⟨T + τ, by linarith, finiteHeatSystemSplice T u v,
      add_nonneg hu.nonneg hτ.le, ?_, ?_, ?_⟩
    · exact continuousOn_finiteHeatSystemSplice hu.nonneg hτ.le hu.continuous hv.continuousOn hinit
    · exact (finiteHeatSystemSplice_zero u v hu.nonneg).trans hu.initial
    · exact hu.equation.splice ha hf hu.nonneg hτ.le hmv hu.continuous hv.continuousOn hinit

/-- At a finite maximal time the endpoint limsup of the norm is infinite.
The limsup is taken in the extended nonnegative reals, so an unbounded
trajectory is not assigned an artificial real-valued limsup. -/
theorem finiteHeatSystem_maximal_limsup
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V)
    (hPQ : ∀ z : V, ∑ i, Q i (P i z) = z)
    (hQP : ∀ i j z, P i (Q j z) = if i = j then z else 0)
    (f : V → V) (hf : ContDiff ℝ ∞ f) (u₀ : BUC E V)
    {R : ℝ} (hR : 0 < R)
    (hmax : localMaximalTime (IsFiniteHeatSystemMildOn a P f hf.continuous) u₀ = ENNReal.ofReal R) :
    Filter.limsup (fun t ↦
      (‖localMaximalTrajectory (IsFiniteHeatSystemMildOn a P f hf.continuous) u₀ t‖₊ : ℝ≥0∞))
      (𝓝[<] R) = (⊤ : ℝ≥0∞) := by
  let sys := finiteHeatSystem_localTrajectorySystem a ha P Q hPQ hQP f hf u₀
  let u := localMaximalTrajectory (IsFiniteHeatSystemMildOn a P f hf.continuous) u₀
  have hu : ContinuousOn u (Ico 0 R) := sys.continuous.mono (fun t ht ↦ by
    refine ⟨ht.1, ?_⟩
    rw [hmax]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr ht.2)
  have hm : ∀ S ∈ Ico 0 R, IsFiniteHeatSystemMildOn a P f hf.continuous S u := by
    intro S hS
    exact (sys.local hS.1 (by rw [hmax]; exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hS.2)).equation
  have hinit : u 0 = u₀ :=
    (sys.local le_rfl (by simpa only [ENNReal.ofReal_zero] using sys.maximalTime_pos)).initial
  apply limsup_enorm_eq_top_of_not_bounded hR hu
  rintro ⟨B, hB, hb⟩
  obtain ⟨S, hS, w, hw, heq, hmw⟩ := exists_finiteHeatSystem_extension_of_bounded
    a ha P Q hPQ hQP f hf hR hB.le hu hb hm
  have hlocal : IsLocalTrajectory (IsFiniteHeatSystemMildOn a P f hf.continuous) u₀ S w :=
    ⟨hR.le.trans hS.le, hw.continuousOn, (heq ⟨le_rfl, hR⟩).symm.trans hinit, hmw⟩
  have hlt := sys.lt_maximalTime hlocal
  rw [hmax] at hlt
  exact (not_lt_of_ge hS.le) ((ENNReal.ofReal_lt_ofReal_iff hR).mp hlt)

/-- Maximal mild existence with exact compatibility and the finite-time
blow-up alternative. All compact restrictions below the lifetime solve
the original coupled equations. -/
theorem exists_maximal_finiteHeatSystem
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → V →L[ℝ] ℝ) (Q : ι → ℝ →L[ℝ] V)
    (hPQ : ∀ z : V, ∑ i, Q i (P i z) = z)
    (hQP : ∀ i j z, P i (Q j z) = if i = j then z else 0)
    (f : V → V) (hf : ContDiff ℝ ∞ f) (u₀ : BUC E V) :
    ∃ T : ℝ≥0∞, 0 < T ∧ ∃ u : ℝ → BUC E V,
      u 0 = u₀ ∧ ContinuousOn u {t | 0 ≤ t ∧ ENNReal.ofReal t < T} ∧
      (∀ S : ℝ, 0 ≤ S → ENNReal.ofReal S < T →
        IsFiniteHeatSystemMildOn a P f hf.continuous S u) ∧
      (∀ (S : ℝ) (v : ℝ → BUC E V), 0 ≤ S → ContinuousOn v (Icc 0 S) → v 0 = u₀ →
        IsFiniteHeatSystemMildOn a P f hf.continuous S v →
        ENNReal.ofReal S < T ∧ EqOn u v (Icc 0 S)) ∧
      ∀ R : ℝ, 0 < R → T = ENNReal.ofReal R →
        Filter.limsup (fun t ↦ (‖u t‖₊ : ℝ≥0∞)) (𝓝[<] R) = (⊤ : ℝ≥0∞) := by
  let sys := finiteHeatSystem_localTrajectorySystem a ha P Q hPQ hQP f hf u₀
  refine ⟨_, sys.maximalTime_pos, _, ?_, sys.continuous, ?_, ?_, ?_⟩
  · exact (sys.local le_rfl (by simpa only [ENNReal.ofReal_zero] using sys.maximalTime_pos)).initial
  · intro S hS hST
    exact (sys.local hS hST).equation
  · intro S v hS hv hinit hmv
    have hh : IsLocalTrajectory (IsFiniteHeatSystemMildOn a P f hf.continuous) u₀ S v :=
      ⟨hS, hv, hinit, hmv⟩
    exact ⟨sys.lt_maximalTime hh, sys.agrees hh⟩
  · intro R hR hmax
    exact finiteHeatSystem_maximal_limsup a ha P Q hPQ hQP f hf u₀ hR hmax

end

end Planarwave
