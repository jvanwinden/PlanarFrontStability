/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCBilinear
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

@[expose] public section

/-!
# Finite-order spatial regularity of BUC trajectories

Each derivative is a genuine BUC field, continuous in time on the specified
set. The recursive formulation lets the scalar-coefficient heat regularity
argument be iterated with Banach-valued derivatives, without postulating
solutions of the formally differentiated equations.
-/

open Set

namespace Planarwave

noncomputable section

universe u v w

variable {E : Type} {F : Type u} {G : Type v} {H : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Spatial derivatives through order `k`, with continuity in the BUC norm in time. -/
def BUCSpatialRegularOn (s : Set ℝ) : (k : ℕ) → {F : Type u} →
    [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℝ → BUC E F) → Prop
  | 0, _, _, _, f => ContinuousOn f s
  | k + 1, F, _, _, f => ContinuousOn f s ∧
      ∃ f' : ℝ → BUC E (E →L[ℝ] F), BUCSpatialRegularOn (F := E →L[ℝ] F) s k f' ∧
        ∀ t ∈ s, ∀ x, HasFDerivAt (f t) (f' t x) x

namespace BUCSpatialRegularOn

theorem continuous {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) : ContinuousOn f s := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

theorem of_succ {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s (k + 1) f) : BUCSpatialRegularOn s k f := by
  induction k generalizing F with
  | zero => exact hf.1
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    exact ⟨hc, f', ih hf', hd⟩

theorem of_le {s : Set ℝ} {j k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) (hjk : j ≤ k) : BUCSpatialRegularOn s j f := by
  induction hjk with
  | refl => exact hf
  | step h ih => exact ih hf.of_succ

theorem congr {s : Set ℝ} {k : ℕ} {f g : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) (heq : EqOn f g s) : BUCSpatialRegularOn s k g := by
  cases k with
  | zero => exact ContinuousOn.congr hf (fun t ht ↦ (heq ht).symm)
  | succ k =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    refine ⟨hc.congr (fun t ht ↦ (heq ht).symm), f', hf', ?_⟩
    intro t ht x
    rw [← heq ht]
    exact hd t ht x

theorem mono {s r : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) (hrs : r ⊆ s) : BUCSpatialRegularOn r k f := by
  induction k generalizing F with
  | zero => exact ContinuousOn.mono hf hrs
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    exact ⟨hc.mono hrs, f', ih hf', fun t ht ↦ hd t (hrs ht)⟩

theorem comp_time {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn univ k f) {r : ℝ → ℝ} (hr : Continuous r) :
    BUCSpatialRegularOn univ k (fun t ↦ f (r t)) := by
  induction k generalizing F with
  | zero => exact ((continuousOn_univ.mp hf).comp hr).continuousOn
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    exact ⟨((continuousOn_univ.mp hc).comp hr).continuousOn, fun t ↦ f' (r t), ih hf',
      fun t _ x ↦ hd (r t) (mem_univ _) x⟩

theorem zero (s : Set ℝ) (k : ℕ) : BUCSpatialRegularOn s k (fun _ ↦ (0 : BUC E F)) := by
  induction k generalizing F with
  | zero => exact continuousOn_const
  | succ k ih =>
    refine ⟨continuousOn_const, fun _ ↦ 0, ih, ?_⟩
    intro t ht x
    simpa only [BUC.coe_zero, BUC.zero_apply] using!
      hasFDerivAt_const (𝕜 := ℝ) (0 : F) x

theorem add {s : Set ℝ} {k : ℕ} {f g : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) (hg : BUCSpatialRegularOn s k g) :
    BUCSpatialRegularOn s k (fun t ↦ f t + g t) := by
  induction k generalizing F with
  | zero => exact hf.add hg
  | succ k ih =>
    obtain ⟨hfc, f', hf', hdf⟩ := hf
    obtain ⟨hgc, g', hg', hdg⟩ := hg
    refine ⟨hfc.add hgc, fun t ↦ f' t + g' t, ih hf' hg', ?_⟩
    intro t ht x
    simpa only [BUC.add_apply] using! (hdf t ht x).add (hdg t ht x)

theorem sum {ι : Type*} (I : Finset ι) {s : Set ℝ} {k : ℕ} {f : ι → ℝ → BUC E F}
    (hf : ∀ i ∈ I, BUCSpatialRegularOn s k (f i)) :
    BUCSpatialRegularOn s k (fun t ↦ ∑ i ∈ I, f i t) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero (E := E) (F := F) s k
  | @insert i I hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

theorem const_smul {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) (c : ℝ) :
    BUCSpatialRegularOn s k (fun t ↦ c • f t) := by
  induction k generalizing F with
  | zero => exact hf.const_smul c
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    refine ⟨hc.const_smul c, fun t ↦ c • f' t, ih hf', ?_⟩
    intro t ht x
    simpa only [BUC.smul_apply] using! (hd t ht x).const_smul c

theorem neg {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) : BUCSpatialRegularOn s k (fun t ↦ -f t) := by
  simpa only [neg_one_smul] using hf.const_smul (-1)

set_option maxHeartbeats 800000 in
/-- The spatial product rule preserves the entire hierarchy of BUC derivatives. -/
theorem bilinear {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F} {g : ℝ → BUC E G}
    (hf : BUCSpatialRegularOn s k f) (hg : BUCSpatialRegularOn s k g)
    (B : F →L[ℝ] G →L[ℝ] H) :
    BUCSpatialRegularOn s k (fun t ↦ BUC.bilinearBUC B (f t) (g t)) := by
  induction k generalizing F G H with
  | zero => exact (BUC.continuous_bilinearBUC B).comp_continuousOn (hf.prodMk hg)
  | succ k ih =>
    obtain ⟨hfc, f', hf', hdf⟩ := hf
    obtain ⟨hgc, g', hg', hdg⟩ := hg
    have hfk : BUCSpatialRegularOn s k f := (show BUCSpatialRegularOn s (k + 1) f from
      ⟨hfc, f', hf', hdf⟩).of_succ
    have hgk : BUCSpatialRegularOn s k g := (show BUCSpatialRegularOn s (k + 1) g from
      ⟨hgc, g', hg', hdg⟩).of_succ
    refine ⟨(BUC.continuous_bilinearBUC B).comp_continuousOn (hfc.prodMk hgc),
      fun t ↦ BUC.bilinearBUC (B.precompR E) (f t) (g' t) +
        BUC.bilinearBUC (B.precompL E) (f' t) (g t),
      (ih hfk hg' (B.precompR E)).add (ih hf' hgk (B.precompL E)), ?_⟩
    intro t ht x
    simpa only [BUC.add_apply, BUC.bilinearBUC_apply] using!
      B.hasFDerivAt_of_bilinear (hdf t ht x) (hdg t ht x)

/-- The recursive BUC witnesses imply ordinary spatial `ContDiff`. -/
theorem contDiff {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) {t : ℝ} (ht : t ∈ s) :
    ContDiff ℝ k (f t : E → F) := by
  induction k generalizing F with
  | zero => exact contDiff_zero.mpr (f t).continuous
  | succ k ih =>
    obtain ⟨_, f', hf', hd⟩ := hf
    exact contDiff_succ_iff_hasFDerivAt.mpr ⟨f' t, ih hf', hd t ht⟩

end BUCSpatialRegularOn

end

end Planarwave
