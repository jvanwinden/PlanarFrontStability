/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace

@[expose] public section

/-!
# Pointwise bilinear operations on BUC spaces

The variable-coefficient longitudinal operator applies the BUC family `f'(φ(z))` pointwise to a
BUC vector.  This file proves once and for all that bounded bilinear operations preserve bounded
uniform continuity, with the expected supremum-norm estimate.
-/

open Filter Function

universe u v w q r

noncomputable section

namespace BUC

variable {A : Type u} [PseudoMetricSpace A]
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
variable {E : Type w} {F : Type q} {G : Type r}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Pointwise application of a continuous bilinear map. -/
def bilinear (B : E →L[𝕜] F →L[𝕜] G) (f : BUC A E) (g : BUC A F) (x : A) : G :=
  B (f x) (g x)

theorem norm_bilinear_apply_le (B : E →L[𝕜] F →L[𝕜] G)
    (f : BUC A E) (g : BUC A F) (x : A) :
    ‖bilinear B f g x‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  calc
    ‖B (f x) (g x)‖ ≤ ‖B (f x)‖ * ‖g x‖ := (B (f x)).le_opNorm (g x)
    _ ≤ (‖B‖ * ‖f x‖) * ‖g x‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm (f x)) (norm_nonneg _)
    _ ≤ (‖B‖ * ‖f‖) * ‖g‖ := by
      gcongr
      · exact f.norm_apply_le x
      · exact g.norm_apply_le x

theorem uniformContinuous_bilinear (B : E →L[𝕜] F →L[𝕜] G)
    (f : BUC A E) (g : BUC A F) : UniformContinuous (bilinear B f g) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  let K : ℝ := ‖B‖ * (‖f‖ + ‖g‖)
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg B) (add_nonneg (norm_nonneg f) (norm_nonneg g))
  let η : ℝ := ε / (2 * (K + 1))
  have hden : 0 < 2 * (K + 1) := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δf, hδf, hf⟩ := Metric.uniformContinuous_iff.mp f.uniformContinuous η hη
  obtain ⟨δg, hδg, hg⟩ := Metric.uniformContinuous_iff.mp g.uniformContinuous η hη
  refine ⟨min δf δg, lt_min hδf hδg, fun x y hxy ↦ ?_⟩
  have hfx : ‖f x - f y‖ < η := by
    simpa [dist_eq_norm] using hf (hxy.trans_le (min_le_left _ _))
  have hgx : ‖g x - g y‖ < η := by
    simpa [dist_eq_norm] using hg (hxy.trans_le (min_le_right _ _))
  rw [dist_eq_norm]
  have hsplit :
      B (f x) (g x) - B (f y) (g y) =
        B (f x) (g x - g y) + B (f x - f y) (g y) := by
    calc
      B (f x) (g x) - B (f y) (g y) =
          (B (f x) (g x) - B (f x) (g y)) +
            (B (f x) (g y) - B (f y) (g y)) := by abel
      _ = B (f x) (g x - g y) + B (f x - f y) (g y) := by simp
  change ‖B (f x) (g x) - B (f y) (g y)‖ < ε
  rw [hsplit]
  calc
    ‖B (f x) (g x - g y) + B (f x - f y) (g y)‖ ≤
        ‖B (f x) (g x - g y)‖ + ‖B (f x - f y) (g y)‖ := norm_add_le _ _
    _ ≤ (‖B‖ * ‖f x‖) * ‖g x - g y‖ +
        (‖B‖ * ‖f x - f y‖) * ‖g y‖ := by
      gcongr
      · exact (B (f x)).le_opNorm _ |>.trans <| by
          gcongr
          exact B.le_opNorm (f x)
      · exact (B (f x - f y)).le_opNorm _ |>.trans <| by
          gcongr
          exact B.le_opNorm (f x - f y)
    _ ≤ (‖B‖ * ‖f‖) * η + (‖B‖ * η) * ‖g‖ := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left (f.norm_apply_le x) (norm_nonneg B)) hgx.le
          (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg f))
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hfx.le (norm_nonneg B)) (g.norm_apply_le y)
          (norm_nonneg _) (mul_nonneg (norm_nonneg B) hη.le)
    _ = K * η := by simp [K]; ring
    _ < ε := by
      dsimp [η]
      rw [show K * (ε / (2 * (K + 1))) = (K / (2 * (K + 1))) * ε by ring]
      have hfrac : K / (2 * (K + 1)) < 1 :=
        (div_lt_one hden).2 (by nlinarith)
      simpa using mul_lt_mul_of_pos_right hfrac hε

/-- Pointwise application of a continuous bilinear map, bundled in BUC. -/
def bilinearBUC (B : E →L[𝕜] F →L[𝕜] G) (f : BUC A E) (g : BUC A F) : BUC A G where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup (bilinear B f g)
    (uniformContinuous_bilinear B f g).continuous (‖B‖ * ‖f‖ * ‖g‖)
    (norm_bilinear_apply_le B f g)
  uniformContinuous' := uniformContinuous_bilinear B f g

@[simp]
theorem bilinearBUC_apply (B : E →L[𝕜] F →L[𝕜] G)
    (f : BUC A E) (g : BUC A F) (x : A) : bilinearBUC B f g x = B (f x) (g x) := rfl

theorem norm_bilinearBUC_le (B : E →L[𝕜] F →L[𝕜] G)
    (f : BUC A E) (g : BUC A F) : ‖bilinearBUC B f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  rw [norm_le (by positivity)]
  exact norm_bilinear_apply_le B f g

/-- For fixed left input, pointwise bilinear application is continuous linear. -/
def bilinearRightCLM (B : E →L[𝕜] F →L[𝕜] G) (f : BUC A E) :
    BUC A F →L[𝕜] BUC A G :=
  LinearMap.mkContinuous
    { toFun := bilinearBUC B f
      map_add' := fun g h ↦ by ext x; simp
      map_smul' := fun c g ↦ by ext x; simp }
    (‖B‖ * ‖f‖) fun g ↦ by
      simpa [mul_assoc] using norm_bilinearBUC_le B f g

@[simp]
theorem bilinearRightCLM_apply (B : E →L[𝕜] F →L[𝕜] G)
    (f : BUC A E) (g : BUC A F) : bilinearRightCLM B f g = bilinearBUC B f g := rfl

/-- Pointwise application of a BUC family of continuous linear maps. -/
def operatorApply (L : BUC A (F →L[𝕜] G)) (f : BUC A F) : BUC A G :=
  bilinearBUC ((ContinuousLinearMap.apply 𝕜 G :
    F →L[𝕜] (F →L[𝕜] G) →L[𝕜] G).flip) L f

@[simp]
theorem operatorApply_apply (L : BUC A (F →L[𝕜] G)) (f : BUC A F) (x : A) :
    operatorApply L f x = L x (f x) := rfl

/-- Variable-coefficient pointwise application as a continuous linear map on BUC. -/
def operatorApplyCLM (L : BUC A (F →L[𝕜] G)) : BUC A F →L[𝕜] BUC A G :=
  bilinearRightCLM ((ContinuousLinearMap.apply 𝕜 G :
    F →L[𝕜] (F →L[𝕜] G) →L[𝕜] G).flip) L

@[simp]
theorem operatorApplyCLM_apply (L : BUC A (F →L[𝕜] G)) (f : BUC A F) :
    operatorApplyCLM L f = operatorApply L f := rfl

end BUC
