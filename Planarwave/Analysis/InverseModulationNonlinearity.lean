/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCNonlinear
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

/-!
# The inverse-modulation nonlinearity and its first estimate

This is the expression `eq:defN` and Lemma 4.1 of the paper, in split coordinates `(y,z)`.
The longitudinal and mixed derivative fields are supplied as BUC data; the
formula and bound are algebraic in those fields. Their identification with the
derivatives of a classical perturbation is recorded separately.
-/

namespace Planarwave

noncomputable section

variable {Y F : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]

/-- Extend a transverse field constantly in the longitudinal direction. -/
def transverseLift {G : Type*} [NormedAddCommGroup G] (v : BUC Y G) : BUC (Y × ℝ) G :=
  v.comp Prod.fst uniformContinuous_fst

omit [InnerProductSpace ℝ Y] in
@[simp]
theorem transverseLift_apply {G : Type*} [NormedAddCommGroup G] (v : BUC Y G) (x : Y × ℝ) :
    transverseLift v x = v x.1 := rfl

omit [InnerProductSpace ℝ Y] in
theorem norm_transverseLift_le {G : Type*} [NormedAddCommGroup G] (v : BUC Y G) :
    ‖transverseLift v‖ ≤ ‖v‖ := BUC.norm_comp_le v _ _

/-- The squared norm of the transverse phase gradient, as a scalar BUC field. -/
def phaseGradientSquared (s : BUC Y Y) : BUC Y ℝ := BUC.bilinearBUC (innerSL ℝ) s s

@[simp]
theorem phaseGradientSquared_apply (s : BUC Y Y) (y : Y) :
    phaseGradientSquared s y = ‖s y‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem norm_phaseGradientSquared_le (s : BUC Y Y) :
    ‖phaseGradientSquared s‖ ≤ ‖s‖ ^ 2 := by
  apply (BUC.norm_le (sq_nonneg _)).mpr
  intro y
  rw [phaseGradientSquared_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (s.norm_apply_le y) 2

/-- The exact nonlinearity `N(v,σ,g)` of the inverse-modulated equation.
Here `vz`, `vzz`, and `vyz` denote `∂z v`, `∂zz v`, and `D_y ∂z v`;
`s` and `l` denote `∇σ` and `Δσ`. -/
def inverseModulationNonlinearity (f : F → F) (hf : ContDiff ℝ 2 f)
    (D : F →L[ℝ] F) (c a : ℝ) (p v vz vzz : BUC (Y × ℝ) F)
    (vyz : BUC (Y × ℝ) (Y →L[ℝ] F)) (s : BUC Y Y) (l g : BUC Y ℝ) : BUC (Y × ℝ) F :=
  BUC.reactionRemainder f hf p v +
    BUC.smulBUC (transverseLift l) (a • vz - BUC.postcompCLM D vz) +
    BUC.smulBUC (transverseLift (phaseGradientSquared s))
      (BUC.postcompCLM D vzz + (c / 2) • vz) -
    (2 : ℝ) • BUC.postcompCLM D (BUC.operatorApply vyz (transverseLift s)) -
    BUC.smulBUC (transverseLift g) vz

/-- Pointwise identification, including the signs of the mixed and forcing terms. -/
theorem inverseModulationNonlinearity_apply (f : F → F) (hf : ContDiff ℝ 2 f)
    (D : F →L[ℝ] F) (c a : ℝ) (p v vz vzz : BUC (Y × ℝ) F)
    (vyz : BUC (Y × ℝ) (Y →L[ℝ] F)) (s : BUC Y Y) (l g : BUC Y ℝ) (x : Y × ℝ) :
    inverseModulationNonlinearity f hf D c a p v vz vzz vyz s l g x =
      f (p x + v x) - f (p x) - fderiv ℝ f (p x) (v x) +
        l x.1 • (a • vz x - D (vz x)) +
        ‖s x.1‖ ^ 2 • (D (vzz x) + (c / 2) • vz x) -
        (2 : ℝ) • D (vyz x (s x.1)) - g x.1 • vz x := by
  simp only [inverseModulationNonlinearity, BUC.add_apply, BUC.sub_apply, BUC.smul_apply,
    BUC.reactionRemainder_apply, BUC.smulBUC_apply, BUC.postcompCLM_apply,
    BUC.operatorApply_apply, transverseLift_apply, phaseGradientSquared_apply]

/-- Estimate each term of `N` separately, as in Lemma 4.1. -/
theorem norm_inverseModulationNonlinearity_le (f : F → F) (hf : ContDiff ℝ 2 f)
    (D : F →L[ℝ] F) (c a : ℝ) (p v vz vzz : BUC (Y × ℝ) F)
    (vyz : BUC (Y × ℝ) (Y →L[ℝ] F)) (s : BUC Y Y) (l g : BUC Y ℝ) :
    ‖inverseModulationNonlinearity f hf D c a p v vz vzz vyz s l g‖ ≤
      ‖BUC.reactionRemainder f hf p v‖ +
        ‖l‖ * ((|a| + ‖D‖) * ‖vz‖) +
        ‖s‖ ^ 2 * (‖D‖ * ‖vzz‖ + |c / 2| * ‖vz‖) +
        2 * ‖D‖ * ‖vyz‖ * ‖s‖ + ‖g‖ * ‖vz‖ := by
  have hl : ‖BUC.smulBUC (transverseLift l) (a • vz - BUC.postcompCLM D vz)‖ ≤
      ‖l‖ * ((|a| + ‖D‖) * ‖vz‖) := by
    have hinner : ‖a • vz - BUC.postcompCLM D vz‖ ≤ (|a| + ‖D‖) * ‖vz‖ := by
      calc
        _ ≤ ‖a • vz‖ + ‖BUC.postcompCLM D vz‖ := norm_sub_le _ _
        _ ≤ |a| * ‖vz‖ + ‖D‖ * ‖vz‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add le_rfl (BUC.norm_postcompCLM_apply_le D vz)
        _ = _ := by ring
    exact (BUC.norm_smulBUC_le _ _).trans
      (mul_le_mul (norm_transverseLift_le l) hinner (norm_nonneg _) (norm_nonneg _))
  have hs : ‖BUC.smulBUC (transverseLift (phaseGradientSquared s))
      (BUC.postcompCLM D vzz + (c / 2) • vz)‖ ≤
      ‖s‖ ^ 2 * (‖D‖ * ‖vzz‖ + |c / 2| * ‖vz‖) := by
    have hinner : ‖BUC.postcompCLM D vzz + (c / 2) • vz‖ ≤
        ‖D‖ * ‖vzz‖ + |c / 2| * ‖vz‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (BUC.norm_postcompCLM_apply_le D vzz) le_rfl
    exact (BUC.norm_smulBUC_le _ _).trans (mul_le_mul
      ((norm_transverseLift_le _).trans (norm_phaseGradientSquared_le s)) hinner
      (norm_nonneg _) (sq_nonneg _))
  have hm : ‖(2 : ℝ) • BUC.postcompCLM D (BUC.operatorApply vyz (transverseLift s))‖ ≤
      2 * ‖D‖ * ‖vyz‖ * ‖s‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * (‖D‖ * (‖vyz‖ * ‖s‖)) :=
        mul_le_mul_of_nonneg_left ((BUC.norm_postcompCLM_apply_le D _).trans
          (mul_le_mul_of_nonneg_left ((BUC.norm_operatorApply_le _ _).trans
            (mul_le_mul_of_nonneg_left (norm_transverseLift_le s) (norm_nonneg vyz)))
            (norm_nonneg D))) (by norm_num)
      _ = _ := by ring
  have hg : ‖BUC.smulBUC (transverseLift g) vz‖ ≤ ‖g‖ * ‖vz‖ :=
    (BUC.norm_smulBUC_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_transverseLift_le g) (norm_nonneg vz))
  exact (norm_sub_le _ _).trans ((add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add le_rfl hl)) hs)) hm)) hg))

/-- Lemma 4.1: the uniform quadratic-plus-derivative estimate for `N`.
The sum of the three derivative norms is bounded by a fixed multiple of the
usual `C²` norm. The constant is chosen before all perturbation and phase fields. -/
theorem exists_inverseModulationNonlinearity_bound (f : F → F) (hf : ContDiff ℝ 2 f)
    (D : F →L[ℝ] F) (c a : ℝ) (p : BUC (Y × ℝ) F) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ v vz vzz : BUC (Y × ℝ) F, ∀ vyz : BUC (Y × ℝ) (Y →L[ℝ] F),
      ∀ s : BUC Y Y, ∀ l g : BUC Y ℝ, ‖v‖ ≤ R →
      ‖inverseModulationNonlinearity f hf D c a p v vz vzz vyz s l g‖ ≤
        C * (‖v‖ ^ 2 + (‖vz‖ + ‖vzz‖ + ‖vyz‖) * (‖l‖ + ‖s‖ + ‖s‖ ^ 2 + ‖g‖)) := by
  obtain ⟨K, hK, hquad⟩ := BUC.exists_reactionRemainder_bound f hf p hR
  let C := K + (|a| + ‖D‖) + (‖D‖ + |c / 2|) + 2 * ‖D‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by dsimp [C]; linarith [norm_nonneg D, abs_nonneg a, abs_nonneg (c / 2)]
  have haC : |a| + ‖D‖ ≤ C := by dsimp [C]; linarith [norm_nonneg D, abs_nonneg (c / 2)]
  have hcC : ‖D‖ + |c / 2| ≤ C := by dsimp [C]; linarith [norm_nonneg D, abs_nonneg a]
  have hDC : 2 * ‖D‖ ≤ C := by dsimp [C]; linarith [norm_nonneg D, abs_nonneg a, abs_nonneg (c / 2)]
  have honeC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg D, abs_nonneg a, abs_nonneg (c / 2)]
  refine ⟨C, hC, fun v vz vzz vyz s l g hv ↦ ?_⟩
  let W := ‖vz‖ + ‖vzz‖ + ‖vyz‖
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hzW : ‖vz‖ ≤ W := by dsimp [W]; linarith [norm_nonneg vzz, norm_nonneg vyz]
  have hzzW : ‖vzz‖ ≤ W := by dsimp [W]; linarith [norm_nonneg vz, norm_nonneg vyz]
  have hyzW : ‖vyz‖ ≤ W := by dsimp [W]; linarith [norm_nonneg vz, norm_nonneg vzz]
  calc
    _ ≤ ‖BUC.reactionRemainder f hf p v‖ + ‖l‖ * ((|a| + ‖D‖) * ‖vz‖) +
        ‖s‖ ^ 2 * (‖D‖ * ‖vzz‖ + |c / 2| * ‖vz‖) +
        2 * ‖D‖ * ‖vyz‖ * ‖s‖ + ‖g‖ * ‖vz‖ :=
      norm_inverseModulationNonlinearity_le f hf D c a p v vz vzz vyz s l g
    _ ≤ K * ‖v‖ ^ 2 + ‖l‖ * ((|a| + ‖D‖) * W) +
        ‖s‖ ^ 2 * ((‖D‖ + |c / 2|) * W) +
        (2 * ‖D‖) * W * ‖s‖ + ‖g‖ * W := by
      have hb : ‖D‖ * ‖vzz‖ + |c / 2| * ‖vz‖ ≤ (‖D‖ + |c / 2|) * W := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hzzW (norm_nonneg D))
          (mul_le_mul_of_nonneg_left hzW (abs_nonneg _))
      gcongr
      exact hquad v hv
    _ ≤ C * ‖v‖ ^ 2 + ‖l‖ * (C * W) + ‖s‖ ^ 2 * (C * W) +
        C * W * ‖s‖ + ‖g‖ * (C * W) := by
      gcongr
      exact le_mul_of_one_le_left hW honeC
    _ = _ := by dsimp [W]; ring

end

end Planarwave
