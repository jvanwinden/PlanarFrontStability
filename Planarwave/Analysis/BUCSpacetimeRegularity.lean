/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCNonlinearHigher
public import Planarwave.Analysis.BUCJointContinuity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Joint regularity of spatial BUC jets

This predicate keeps the closed-slab BUC continuity of every spatial
derivative together with its joint regularity on the open slab. It is
suited to the time/spatial derivative induction in the parabolic bootstrap.
-/

open Set
open scoped ContDiff

namespace Planarwave

noncomputable section

universe u v w

variable {E : Type} {F : Type u} {G : Type v} {H : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Spatial jets through order `j`, each continuous in BUC on the closed
slab and jointly `C^k` on its interior. -/
def BUCSpacetimeRegularOn (a b : ℝ) (k : ℕ) : (j : ℕ) → {F : Type u} →
    [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℝ → BUC E F) → Prop
  | 0, _, _, _, f => ContinuousOn f (Icc a b) ∧
      ContDiffOn ℝ k (fun p : ℝ × E ↦ f p.1 p.2) (Ioo a b ×ˢ univ)
  | j + 1, F, _, _, f => ContinuousOn f (Icc a b) ∧
      ContDiffOn ℝ k (fun p : ℝ × E ↦ f p.1 p.2) (Ioo a b ×ˢ univ) ∧
      ∃ f' : ℝ → BUC E (E →L[ℝ] F), BUCSpacetimeRegularOn a b k j f' ∧
        ∀ t ∈ Icc a b, ∀ x, HasFDerivAt (f t) (f' t x) x

namespace BUCSpacetimeRegularOn

theorem continuous {a b : ℝ} {k j : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k j f) : ContinuousOn f (Icc a b) := by
  cases j <;> exact hf.1

theorem joint {a b : ℝ} {k j : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k j f) :
    ContDiffOn ℝ k (fun p : ℝ × E ↦ f p.1 p.2) (Ioo a b ×ˢ univ) := by
  cases j with
  | zero => exact hf.2
  | succ j => exact hf.2.1

theorem spatialRegular {a b : ℝ} {k j : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k j f) : BUCSpatialRegularOn (Icc a b) j f := by
  induction j generalizing F with
  | zero => exact hf.1
  | succ j ih =>
    obtain ⟨hc, _, f', hf', hd⟩ := hf
    exact ⟨hc, f', ih hf', hd⟩

theorem of_succ {a b : ℝ} {k j : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k (j + 1) f) : BUCSpacetimeRegularOn a b k j f := by
  induction j generalizing F with
  | zero => exact ⟨hf.1, hf.2.1⟩
  | succ j ih =>
    obtain ⟨hc, hj, f', hf', hd⟩ := hf
    exact ⟨hc, hj, f', ih hf', hd⟩

theorem of_le {a b : ℝ} {k i j : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k j f) (hij : i ≤ j) :
    BUCSpacetimeRegularOn a b k i f := by
  induction hij with
  | refl => exact hf
  | step h ih => exact ih hf.of_succ

theorem congr {a b : ℝ} {k j : ℕ} {f g : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k j f) (heq : EqOn f g (Icc a b)) :
    BUCSpacetimeRegularOn a b k j g := by
  have hc := hf.continuous.congr (fun t ht ↦ (heq ht).symm)
  have hj := hf.joint.congr (fun p hp ↦ congrArg (fun z : BUC E F ↦ z p.2)
    (heq (Ioo_subset_Icc_self hp.1)).symm)
  cases j with
  | zero => exact ⟨hc, hj⟩
  | succ j =>
    obtain ⟨_, _, f', hf', hd⟩ := hf
    refine ⟨hc, hj, f', hf', ?_⟩
    intro t ht x
    rw [← heq ht]
    exact hd t ht x

/-- A prescribed genuine spatial derivative inherits the jet regularity;
the choice of the recursive witness is immaterial. -/
theorem derivative {a b : ℝ} {k j : ℕ} {f : ℝ → BUC E F}
    {q : ℝ → BUC E (E →L[ℝ] F)} (hf : BUCSpacetimeRegularOn a b k (j + 1) f)
    (hd : ∀ t ∈ Icc a b, ∀ x, HasFDerivAt (f t) (q t x) x) :
    BUCSpacetimeRegularOn a b k j q := by
  obtain ⟨_, _, f', hf', hdf⟩ := hf
  exact hf'.congr (fun t ht ↦ BUC.ext fun x ↦ (hdf t ht x).unique (hd t ht x))

theorem of_spatialRegular {a b : ℝ} {j : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn (Icc a b) j f) : BUCSpacetimeRegularOn a b 0 j f := by
  have hj : ContDiffOn ℝ 0 (fun p : ℝ × E ↦ f p.1 p.2) (Ioo a b ×ˢ univ) := contDiffOn_zero.mpr
    (BUC.continuousOn_uncurry (hf.continuous.mono Ioo_subset_Icc_self))
  induction j generalizing F with
  | zero => exact ⟨hf, hj⟩
  | succ j ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    exact ⟨hc, hj, f', ih hf' (contDiffOn_zero.mpr
      (BUC.continuousOn_uncurry (hf'.continuous.mono Ioo_subset_Icc_self))), hd⟩

theorem add {a b : ℝ} {k j : ℕ} {f g : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k j f) (hg : BUCSpacetimeRegularOn a b k j g) :
    BUCSpacetimeRegularOn a b k j (fun t ↦ f t + g t) := by
  have hc := hf.continuous.add hg.continuous
  have hj : ContDiffOn ℝ k (fun p : ℝ × E ↦ (f p.1 + g p.1) p.2)
      (Ioo a b ×ˢ univ) := hf.joint.add hg.joint
  induction j generalizing F with
  | zero => exact ⟨hc, hj⟩
  | succ j ih =>
    obtain ⟨_, _, f', hf', hdf⟩ := hf
    obtain ⟨_, _, g', hg', hdg⟩ := hg
    refine ⟨hc, hj, fun t ↦ f' t + g' t, ih hf' hg'
      (hf'.continuous.add hg'.continuous) (hf'.joint.add hg'.joint), ?_⟩
    intro t ht x
    simpa only [BUC.add_apply] using! (hdf t ht x).add (hdg t ht x)

/-- The spatial product rule also preserves joint regularity of every jet. -/
theorem bilinear {a b : ℝ} {k j : ℕ} {f : ℝ → BUC E F} {g : ℝ → BUC E G}
    (hf : BUCSpacetimeRegularOn a b k j f) (hg : BUCSpacetimeRegularOn a b k j g)
    (B : F →L[ℝ] G →L[ℝ] H) :
    BUCSpacetimeRegularOn a b k j (fun t ↦ BUC.bilinearBUC B (f t) (g t)) := by
  induction j generalizing F G H with
  | zero =>
    exact ⟨(BUC.continuous_bilinearBUC B).comp_continuousOn
      (hf.continuous.prodMk hg.continuous),
      (B.contDiff.comp_contDiffOn hf.joint).clm_apply hg.joint⟩
  | succ j ih =>
    have hfj := hf.of_succ
    have hgj := hg.of_succ
    obtain ⟨hfc, hfjc, f', hf', hdf⟩ := hf
    obtain ⟨hgc, hgjc, g', hg', hdg⟩ := hg
    refine ⟨(BUC.continuous_bilinearBUC B).comp_continuousOn (hfc.prodMk hgc),
      (B.contDiff.comp_contDiffOn hfjc).clm_apply hgjc,
      fun t ↦ BUC.bilinearBUC (B.precompR E) (f t) (g' t) +
        BUC.bilinearBUC (B.precompL E) (f' t) (g t),
      (ih hfj hg' (B.precompR E)).add (ih hf' hgj (B.precompL E)), ?_⟩
    intro t ht x
    simpa only [BUC.add_apply, BUC.bilinearBUC_apply] using!
      B.hasFDerivAt_of_bilinear (hdf t ht x) (hdg t ht x)

/-- Continuous linear postcomposition preserves every spatial and joint order. -/
theorem postcompCLM {a b : ℝ} {k j : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpacetimeRegularOn a b k j f) (L : F →L[ℝ] G) :
    BUCSpacetimeRegularOn a b k j (fun t ↦ BUC.postcompCLM L (f t)) := by
  induction j generalizing F G with
  | zero =>
    exact ⟨(BUC.postcompCLM L).continuous.comp_continuousOn hf.continuous,
      L.contDiff.comp_contDiffOn hf.joint⟩
  | succ j ih =>
    obtain ⟨hc, hj, f', hf', hd⟩ := hf
    let J := ContinuousLinearMap.compL ℝ E F G L
    refine ⟨(BUC.postcompCLM L).continuous.comp_continuousOn hc,
      L.contDiff.comp_contDiffOn hj, fun t ↦ BUC.postcompCLM J (f' t), ih hf' J, ?_⟩
    intro t ht x
    simpa only [BUC.postcompCLM_apply, J, ContinuousLinearMap.compL_apply] using!
      L.hasFDerivAt.comp x (hd t ht x)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]

/-- Smooth nonlinear substitution preserves the joint regularity of spatial jets. -/
theorem postcomp_smooth {a b : ℝ} {k j : ℕ} {u : ℝ → BUC E V}
    (hu : BUCSpacetimeRegularOn a b k j u) (f : V → F) (hf : ContDiff ℝ ∞ f) :
    BUCSpacetimeRegularOn a b k j (fun t ↦ BUC.postcompContinuous f hf.continuous (u t)) := by
  induction j generalizing F with
  | zero =>
    exact ⟨(BUC.continuous_postcompContinuous f (hf.of_le (by simp))).comp_continuousOn hu.continuous,
      (hf.of_le (by exact_mod_cast le_top)).comp_contDiffOn hu.joint⟩
  | succ j ih =>
    have huj := hu.of_succ
    obtain ⟨hc, hj, q, hq, hd⟩ := hu
    have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    let J := ContinuousLinearMap.compL ℝ E V F
    refine ⟨(BUC.continuous_postcompContinuous f (hf.of_le (by simp))).comp_continuousOn hc,
      (hf.of_le (by exact_mod_cast le_top)).comp_contDiffOn hj,
      fun t ↦ BUC.bilinearBUC J (BUC.postcompContinuous (fderiv ℝ f) hf'.continuous (u t)) (q t),
      (ih huj (fderiv ℝ f) hf').bilinear hq J, ?_⟩
    intro t ht x
    exact (hf.differentiable (by simp) (u t x)).hasFDerivAt.comp x (hd t ht x)

end BUCSpacetimeRegularOn

end

end Planarwave
