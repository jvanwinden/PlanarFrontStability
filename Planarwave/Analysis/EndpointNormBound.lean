/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

/-!
# Finite endpoint norm bounds

In the final proof of the paper, the continuation criterion is applied
to the norm of a solution as time approaches its finite maximal endpoint.
A finite extended-real limsup gives an eventual bound near the endpoint;
continuity supplies the bound on the remaining compact initial interval.
The limsup is taken in `ℝ≥0∞`, so unbounded norms cannot accidentally have
a finite limsup by the convention for conditionally complete orders.
-/

open Filter Set
open scoped Topology NNReal ENNReal

namespace Planarwave

variable {X : Type*} [NormedAddCommGroup X] {u : ℝ → X} {T B : ℝ}

/-- An eventual norm bound at a finite right endpoint, together with
continuity on the half-open interval, bounds the entire trajectory. -/
theorem exists_pos_bound_Ico_of_eventually_norm_le
    (hT : 0 < T) (hu : ContinuousOn u (Ico 0 T))
    (hbound : ∀ᶠ t in 𝓝[<] T, ‖u t‖ ≤ B) :
    ∃ C > 0, ∀ t ∈ Ico 0 T, ‖u t‖ ≤ C := by
  obtain ⟨a, haT, ha⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hbound
  let c := max 0 a
  have hcT : c < T := max_lt hT haT
  have huc : ContinuousOn u (Icc 0 c) := hu.mono fun t ht ↦
    ⟨ht.1, ht.2.trans_lt hcT⟩
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
  refine ⟨max (max C₀ B) 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro t ht
  by_cases htc : t ≤ c
  · exact (hC₀ t ⟨ht.1, htc⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (ha ⟨(le_max_right 0 a).trans_lt (lt_of_not_ge htc), ht.2⟩).trans
      ((le_max_right _ _).trans (le_max_left _ _))

/-- A finite extended limsup of the norm yields a finite real norm bound
on a left-hand neighborhood of the endpoint. No boundedness assumption
is needed in the complete order `ℝ≥0∞`. -/
theorem eventually_norm_le_of_limsup_enorm_lt_top
    (hlim : limsup (fun t ↦ (‖u t‖₊ : ℝ≥0∞)) (𝓝[<] T) < ∞) :
    ∃ B : ℝ, ∀ᶠ t in 𝓝[<] T, ‖u t‖ ≤ B := by
  obtain ⟨R, hR, _⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlim
  refine ⟨R, (eventually_lt_of_limsup_lt hR).mono fun t ht ↦ ?_⟩
  exact NNReal.coe_le_coe.mpr (ENNReal.coe_lt_coe.mp ht).le

/-- The bounded-norm continuation hypothesis follows from the finite
extended limsup used in the paper's blow-up alternative. -/
theorem exists_pos_bound_Ico_of_limsup_enorm_lt_top
    (hT : 0 < T) (hu : ContinuousOn u (Ico 0 T))
    (hlim : limsup (fun t ↦ (‖u t‖₊ : ℝ≥0∞)) (𝓝[<] T) < ∞) :
    ∃ C > 0, ∀ t ∈ Ico 0 T, ‖u t‖ ≤ C := by
  obtain ⟨B, hB⟩ := eventually_norm_le_of_limsup_enorm_lt_top hlim
  exact exists_pos_bound_Ico_of_eventually_norm_le hT hu hB

/-- If no uniform norm bound exists before a finite endpoint, its
extended limsup is infinite. This is the form used after a bounded
continuation theorem contradicts maximality. -/
theorem limsup_enorm_eq_top_of_not_bounded
    (hT : 0 < T) (hu : ContinuousOn u (Ico 0 T))
    (hunbounded : ¬ ∃ C > 0, ∀ t ∈ Ico 0 T, ‖u t‖ ≤ C) :
    limsup (fun t ↦ (‖u t‖₊ : ℝ≥0∞)) (𝓝[<] T) = ∞ := by
  by_contra h
  exact hunbounded (exists_pos_bound_Ico_of_limsup_enorm_lt_top hT hu
    (lt_top_iff_ne_top.mpr h))

end Planarwave
