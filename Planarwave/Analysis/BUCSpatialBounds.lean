/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialRegularity
public import Planarwave.Analysis.BUCNonlinear
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-!
# Common bounds for genuine spatial derivative fields

The maximum of derivative norms through order `k` is represented by its
upper-bound predicate. This avoids choosing derivative fields before their
existence is proved. Product rules cost at most `2^k`; a regular trajectory
has a continuous, least such upper bound, suitable for integral Grönwall.
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

/-- Every genuine BUC derivative through order `k` has norm at most `A`. -/
def BUCSpatialBound : (k : ℕ) → {F : Type u} →
    [NormedAddCommGroup F] → [NormedSpace ℝ F] → BUC E F → ℝ → Prop
  | 0, _, _, _, f, A => ‖f‖ ≤ A
  | k + 1, F, _, _, f, A => ‖f‖ ≤ A ∧
      ∃ f' : BUC E (E →L[ℝ] F), BUCSpatialBound k f' A ∧
        ∀ x, HasFDerivAt f (f' x) x

namespace BUCSpatialBound

theorem norm_le {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A) : ‖f‖ ≤ A := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

theorem nonneg {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A) : 0 ≤ A :=
  (norm_nonneg f).trans hf.norm_le

theorem mono {k : ℕ} {f : BUC E F} {A B : ℝ} (hf : BUCSpatialBound k f A) (hAB : A ≤ B) :
    BUCSpatialBound k f B := by
  induction k generalizing F with
  | zero => exact hf.trans hAB
  | succ k ih =>
    obtain ⟨hn, f', hf', hd⟩ := hf
    exact ⟨hn.trans hAB, f', ih hf', hd⟩

theorem of_succ {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound (k + 1) f A) :
    BUCSpatialBound k f A := by
  induction k generalizing F with
  | zero => exact hf.1
  | succ k ih =>
    obtain ⟨hn, f', hf', hd⟩ := hf
    exact ⟨hn, f', ih hf', hd⟩

theorem derivative {k : ℕ} {f : BUC E F} {f' : BUC E (E →L[ℝ] F)} {A : ℝ}
    (hf : BUCSpatialBound (k + 1) f A) (hd : ∀ x, HasFDerivAt f (f' x) x) :
    BUCSpatialBound k f' A := by
  obtain ⟨_, g, hg, hdg⟩ := hf
  have heq : g = f' := BUC.ext fun x ↦ (hdg x).unique (hd x)
  rwa [← heq]

theorem add {k : ℕ} {f g : BUC E F} {A B : ℝ}
    (hf : BUCSpatialBound k f A) (hg : BUCSpatialBound k g B) :
    BUCSpatialBound k (f + g) (A + B) := by
  induction k generalizing F with
  | zero => exact (norm_add_le _ _).trans (add_le_add hf hg)
  | succ k ih =>
    obtain ⟨hfn, f', hf', hdf⟩ := hf
    obtain ⟨hgn, g', hg', hdg⟩ := hg
    refine ⟨(norm_add_le _ _).trans (add_le_add hfn hgn), f' + g', ih hf' hg', ?_⟩
    intro x
    simpa only [BUC.add_apply] using! (hdf x).add (hdg x)

theorem smul {k : ℕ} {f : BUC E F} {A : ℝ}
    (hf : BUCSpatialBound k f A) (c : ℝ) : BUCSpatialBound k (c • f) (|c| * A) := by
  induction k generalizing F with
  | zero =>
    change ‖c • f‖ ≤ |c| * A
    simpa only [norm_smul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hf (abs_nonneg c)
  | succ k ih =>
    obtain ⟨hn, f', hf', hd⟩ := hf
    refine ⟨?_, c • f', ih hf', ?_⟩
    · simpa only [norm_smul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hn (abs_nonneg c)
    · intro x
      simpa only [BUC.smul_apply] using! (hd x).const_smul c

theorem neg {k : ℕ} {f : BUC E F} {A : ℝ}
    (hf : BUCSpatialBound k f A) : BUCSpatialBound k (-f) A := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using hf.smul (-1)

set_option maxHeartbeats 800000 in
/-- The repeated product rule, with one constant for all derivatives. -/
theorem bilinear {k : ℕ} {f : BUC E F} {g : BUC E G} {A C : ℝ}
    (hf : BUCSpatialBound k f A) (hg : BUCSpatialBound k g C)
    (B : F →L[ℝ] G →L[ℝ] H) :
    BUCSpatialBound k (BUC.bilinearBUC B f g) ((2 : ℝ) ^ k * ‖B‖ * A * C) := by
  have hA := hf.nonneg
  have hC := hg.nonneg
  induction k generalizing F G H with
  | zero =>
    change ‖BUC.bilinearBUC B f g‖ ≤ _
    simpa only [pow_zero, one_mul] using
      (BUC.norm_bilinearBUC_le B f g).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg
          (norm_nonneg _) (mul_nonneg (norm_nonneg B) hA))
  | succ k ih =>
    have hfk := hf.of_succ
    have hgk := hg.of_succ
    obtain ⟨hfn, f', hf', hdf⟩ := hf
    obtain ⟨hgn, g', hg', hdg⟩ := hg
    have hR := (ih hfk hg' (B.precompR E)).mono
      (B := (2 : ℝ) ^ k * ‖B‖ * A * C) (by
        gcongr; exact ContinuousLinearMap.norm_precompR_le E B)
    have hL := (ih hf' hgk (B.precompL E)).mono
      (B := (2 : ℝ) ^ k * ‖B‖ * A * C) (by
        gcongr; exact ContinuousLinearMap.norm_precompL_le E B)
    refine ⟨?_, BUC.bilinearBUC (B.precompR E) f g' + BUC.bilinearBUC (B.precompL E) f' g,
      ?_, ?_⟩
    · calc
        _ ≤ ‖B‖ * A * C := (BUC.norm_bilinearBUC_le B f g).trans (by gcongr)
        _ ≤ (2 : ℝ) ^ (k + 1) * ‖B‖ * A * C := by
          have hpow : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hpow (show 0 ≤ ‖B‖ * A * C by positivity)]
    · convert hR.add hL using 1
      ring
    · intro x
      simpa only [BUC.add_apply, BUC.bilinearBUC_apply] using!
        B.hasFDerivAt_of_bilinear (hdf x) (hdg x)

/-- Scalar multiplication of fields, including a possibly trivial target space. -/
theorem smulBUC {k : ℕ} {f : BUC E ℝ} {g : BUC E F} {A B : ℝ}
    (hf : BUCSpatialBound k f A) (hg : BUCSpatialBound k g B) :
    BUCSpatialBound k (BUC.smulBUC f g) ((2 : ℝ) ^ k * A * B) := by
  apply (hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ)).mono
  calc
    _ ≤ (2 : ℝ) ^ k * 1 * A * B := by
      gcongr
      · exact hg.nonneg
      · exact hf.nonneg
      · exact ContinuousLinearMap.opNorm_lsmul_le
    _ = _ := by ring

/-- Bounds on the BUC derivative fields bound the standard iterated Fréchet derivatives. -/
theorem norm_iteratedFDeriv_le {k j : ℕ} {f : BUC E F} {A : ℝ}
    (hf : BUCSpatialBound k f A) (hj : j ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ j (f : E → F) x‖ ≤ A := by
  induction j generalizing k F with
  | zero => simpa only [norm_iteratedFDeriv_zero] using (f.norm_apply_le x).trans hf.norm_le
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨_, f', hf', hd⟩ := hf
      have heq : fderiv ℝ (f : E → F) = f' := funext fun y ↦ (hd y).fderiv
      rw [← norm_iteratedFDeriv_fderiv, heq]
      exact ih hf' (by omega)

end BUCSpatialBound

/-- A regular trajectory has a continuous maximum of its derivative norms.
The minimality clause justifies using any proved common bound in Grönwall. -/
theorem BUCSpatialRegularOn.exists_least_bound {s : Set ℝ} {k : ℕ} {f : ℝ → BUC E F}
    (hf : BUCSpatialRegularOn s k f) :
    ∃ U : ℝ → ℝ, ContinuousOn U s ∧ ∀ t ∈ s,
      BUCSpatialBound k (f t) (U t) ∧ ∀ A, BUCSpatialBound k (f t) A → U t ≤ A := by
  induction k generalizing F with
  | zero => exact ⟨fun t ↦ ‖f t‖, hf.norm, fun _ _ ↦ ⟨le_rfl, fun _ h ↦ h⟩⟩
  | succ k ih =>
    obtain ⟨hc, f', hf', hd⟩ := hf
    obtain ⟨V, hVc, hV⟩ := ih hf'
    refine ⟨fun t ↦ max ‖f t‖ (V t), hc.norm.sup hVc, ?_⟩
    intro t ht
    refine ⟨⟨le_max_left _ _, f' t, (hV t ht).1.mono (le_max_right _ _), hd t ht⟩, ?_⟩
    intro A hA
    exact max_le hA.norm_le ((hV t ht).2 A (hA.derivative (hd t ht)))

/-- Pointwise bounds on all standard derivatives recover the BUC common-bound predicate. -/
theorem BUCSpatialRegularOn.bound_of_iteratedFDeriv {s : Set ℝ} {k : ℕ}
    {f : ℝ → BUC E F} (hf : BUCSpatialRegularOn s k f) {t A : ℝ} (ht : t ∈ s)
    (hb : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (f t : E → F) x‖ ≤ A) :
    BUCSpatialBound k (f t) A := by
  have h0 : ∀ x, ‖f t x‖ ≤ A := by simpa only [norm_iteratedFDeriv_zero] using hb 0 (Nat.zero_le k)
  have hA : 0 ≤ A := (norm_nonneg _).trans (h0 0)
  have hn : ‖f t‖ ≤ A := (BUC.norm_le hA).mpr h0
  clear h0
  induction k generalizing F with
  | zero => exact hn
  | succ k ih =>
    obtain ⟨_, f', hf', hd⟩ := hf
    refine ⟨hn, f' t, ?_, hd t ht⟩
    have hnext : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (f' t : E → E →L[ℝ] F) x‖ ≤ A := by
      intro j hj x
      have heq : (f' t : E → E →L[ℝ] F) = fderiv ℝ (f t : E → F) :=
        funext fun y ↦ (hd t ht y).fderiv.symm
      rw [heq, norm_iteratedFDeriv_fderiv]
      exact hb (j + 1) (Nat.succ_le_succ hj) x
    exact ih hf' hnext ((BUC.norm_le hA).mpr (fun x ↦ by
      simpa only [norm_iteratedFDeriv_zero] using hnext 0 (Nat.zero_le k) x))

end

end Planarwave
