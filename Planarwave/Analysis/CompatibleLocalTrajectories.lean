/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.ContinuousOn

@[expose] public section

/-!
# Maximal trajectories from compatible local solutions

The maximal trajectory is the union of the compatible local solutions with
one fixed initial value. Its lifetime is the supremum of their lifetimes.
Local continuation ensures that no admissible endpoint is maximal.
-/

open Set Filter
open scoped Topology ENNReal

namespace Planarwave

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- A continuous solution on a closed, nonnegative time interval. -/
structure IsLocalTrajectory (P : ℝ → (ℝ → X) → Prop) (x₀ : X)
    (T : ℝ) (u : ℝ → X) : Prop where
  nonneg : 0 ≤ T
  continuous : ContinuousOn u (Icc 0 T)
  initial : u 0 = x₀
  equation : P T u

/-- The compatibility and local continuation properties used in the standard
construction of a maximal solution. -/
structure LocalTrajectorySystem (P : ℝ → (ℝ → X) → Prop) (x₀ : X) : Prop where
  positive : ∃ T > 0, ∃ u, IsLocalTrajectory P x₀ T u
  mono : ∀ {S T u}, 0 ≤ S → S ≤ T → P T u → P S u
  congr : ∀ {T u v}, EqOn u v (Icc 0 T) → P T u → P T v
  compatible : ∀ {S T u v}, IsLocalTrajectory P x₀ S u →
    IsLocalTrajectory P x₀ T v → EqOn u v (Icc 0 (min S T))
  extend : ∀ {T u}, IsLocalTrajectory P x₀ T u →
    ∃ S > T, ∃ v, IsLocalTrajectory P x₀ S v

/-- The supremum of the lengths of the local solution intervals. -/
def localMaximalTime (P : ℝ → (ℝ → X) → Prop) (x₀ : X) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {T | ∃ u, IsLocalTrajectory P x₀ T u})

/-- At a time covered by some local solution, choose the value of one such
solution. Compatibility will show that this choice is immaterial. -/
def localMaximalTrajectory (P : ℝ → (ℝ → X) → Prop) (x₀ : X) (t : ℝ) : X := by
  classical
  exact if h : ∃ T, ∃ u, IsLocalTrajectory P x₀ T u ∧ t ∈ Icc 0 T then
    h.choose_spec.choose t
  else x₀

variable {P : ℝ → (ℝ → X) → Prop} {x₀ : X}

namespace LocalTrajectorySystem

variable (sys : LocalTrajectorySystem P x₀)

include sys

/-- A local solution has lifetime below or equal to the supremum. -/
theorem le_maximalTime {T : ℝ} {u : ℝ → X} (hu : IsLocalTrajectory P x₀ T u) :
    ENNReal.ofReal T ≤ localMaximalTime P x₀ :=
  le_sSup ⟨T, ⟨u, hu⟩, rfl⟩

/-- Local continuation makes the inequality strict at every closed local
solution interval. -/
theorem lt_maximalTime {T : ℝ} {u : ℝ → X} (hu : IsLocalTrajectory P x₀ T u) :
    ENNReal.ofReal T < localMaximalTime P x₀ := by
  obtain ⟨S, hST, v, hv⟩ := sys.extend hu
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.nonneg).2 hST).trans_le
    (sys.le_maximalTime hv)

theorem maximalTime_pos : 0 < localMaximalTime P x₀ := by
  obtain ⟨T, hT, u, hu⟩ := sys.positive
  exact (ENNReal.ofReal_pos.2 hT).trans_le (sys.le_maximalTime hu)

/-- Every time strictly before the supremum is covered by a longer local
solution interval. -/
theorem exists_local_after {t : ℝ} (ht : 0 ≤ t)
    (hmax : ENNReal.ofReal t < localMaximalTime P x₀) :
    ∃ T > t, ∃ u, IsLocalTrajectory P x₀ T u := by
  obtain ⟨r, ⟨T, ⟨u, hu⟩, rfl⟩, hr⟩ := lt_sSup_iff.mp hmax
  exact ⟨T, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 hr, u, hu⟩

/-- The canonical trajectory agrees with every local solution, including
both endpoints of that local solution's interval. -/
theorem agrees {T : ℝ} {u : ℝ → X} (hu : IsLocalTrajectory P x₀ T u) :
    EqOn (localMaximalTrajectory P x₀) u (Icc 0 T) := by
  intro t ht
  have hex : ∃ S, ∃ v, IsLocalTrajectory P x₀ S v ∧ t ∈ Icc 0 S :=
    ⟨T, u, hu, ht⟩
  rw [localMaximalTrajectory, dif_pos hex]
  have hchosen := hex.choose_spec.choose_spec
  exact sys.compatible hchosen.1 hu
    ⟨ht.1, le_min hchosen.2.2 ht.2⟩

/-- The canonical trajectory solves the equation on every compact time
interval strictly before the maximal lifetime. -/
theorem «local» {S : ℝ} (hS : 0 ≤ S)
    (hmax : ENNReal.ofReal S < localMaximalTime P x₀) :
    IsLocalTrajectory P x₀ S (localMaximalTrajectory P x₀) := by
  obtain ⟨T, hST, u, hu⟩ := sys.exists_local_after hS hmax
  have hsub : Icc 0 S ⊆ Icc 0 T := Icc_subset_Icc_right hST.le
  have heq := (sys.agrees hu).mono hsub
  exact ⟨hS, (hu.continuous.mono hsub).congr heq,
    (heq ⟨le_rfl, hS⟩).trans hu.initial,
    sys.congr heq.symm (sys.mono hS hST.le hu.equation)⟩

theorem initial : localMaximalTrajectory P x₀ 0 = x₀ := by
  obtain ⟨T, hT, u, hu⟩ := sys.positive
  exact (sys.agrees hu ⟨le_rfl, hT.le⟩).trans hu.initial

/-- Continuity holds on the whole maximal half-open interval, including
right continuity at the initial time. -/
theorem continuous : ContinuousOn (localMaximalTrajectory P x₀)
    {t | 0 ≤ t ∧ ENNReal.ofReal t < localMaximalTime P x₀} := by
  intro t ht
  obtain ⟨T, htT, u, hu⟩ := sys.exists_local_after ht.1 ht.2
  have hcont : ContinuousOn (localMaximalTrajectory P x₀) (Icc 0 T) :=
    hu.continuous.congr (sys.agrees hu)
  apply (hcont t ⟨ht.1, htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with r hr hrT
  exact ⟨hr.1, hrT.le⟩

end LocalTrajectorySystem

end

end Planarwave
