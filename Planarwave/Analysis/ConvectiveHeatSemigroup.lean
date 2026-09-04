/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Planarwave.Analysis.HeatSemigroup

@[expose] public section

/-!
# The convective heat semigroup on bounded uniformly continuous functions

The proof of Lemma 2.2 in the cited paper begins with the classical contraction bound for
`exp (t (a Δ + b · ∇))`.  This file realizes that evolution as Gaussian heat flow followed by
translation, and proves its linearity, contraction estimate, and semigroup law.
-/

namespace Planarwave

noncomputable section

open MeasureTheory ProbabilityTheory

section ConvectiveHeat

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Gaussian heat flow with constant drift.  The sign is chosen so that the translation is
`f(x + t b)`, corresponding to the generator `a Δ + b · ∇`. -/
def convectiveHeatFlowBUC (a t : ℝ) (b : E) (f : BUC E F) : BUC E F :=
  BUC.translate (-(t • b)) (heatFlowBUC a t f)

@[simp]
theorem convectiveHeatFlowBUC_apply (a t : ℝ) (b : E) (f : BUC E F) (x : E) :
    convectiveHeatFlowBUC a t b f x = heatFlow a t f (x + t • b) := by
  simp [convectiveHeatFlowBUC]

@[simp]
theorem convectiveHeatFlowBUC_zero (a : ℝ) (b : E) (f : BUC E F) :
    convectiveHeatFlowBUC a 0 b f = f := by
  simp [convectiveHeatFlowBUC]

theorem convectiveHeatFlowBUC_add (a t : ℝ) (b : E) (f g : BUC E F) :
    convectiveHeatFlowBUC a t b (f + g) =
      convectiveHeatFlowBUC a t b f + convectiveHeatFlowBUC a t b g := by
  ext x
  simp [convectiveHeatFlowBUC, heatFlowBUC_add]

theorem convectiveHeatFlowBUC_smul (a t r : ℝ) (b : E) (f : BUC E F) :
    convectiveHeatFlowBUC a t b (r • f) = r • convectiveHeatFlowBUC a t b f := by
  ext x
  simp [convectiveHeatFlowBUC, heatFlowBUC_smul]

/-- Convective heat flow is a contraction in the supremum norm. -/
theorem norm_convectiveHeatFlowBUC_le (a t : ℝ) (b : E) (f : BUC E F) :
    ‖convectiveHeatFlowBUC a t b f‖ ≤ ‖f‖ := by
  rw [convectiveHeatFlowBUC, BUC.norm_translate]
  exact norm_heatFlowBUC_le a t f

/-- Translation preserves distances in `BUC`. -/
theorem dist_translate_eq (b : E) (f g : BUC E F) :
    dist (BUC.translate b f) (BUC.translate b g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : BUC.translate b f - BUC.translate b g = BUC.translate b (f - g) := by
    ext x
    rfl
  rw [hsub, BUC.norm_translate]

/-- The convective heat evolution as a continuous linear contraction. -/
def convectiveHeatOperator (a t : ℝ) (b : E) : BUC E F →L[ℝ] BUC E F :=
  LinearMap.mkContinuous
    { toFun := convectiveHeatFlowBUC a t b
      map_add' := convectiveHeatFlowBUC_add a t b
      map_smul' := fun r f ↦ convectiveHeatFlowBUC_smul a t r b f }
    1 (fun f ↦ by simpa using norm_convectiveHeatFlowBUC_le a t b f)

@[simp]
theorem convectiveHeatOperator_apply (a t : ℝ) (b : E) (f : BUC E F) :
    convectiveHeatOperator a t b f = convectiveHeatFlowBUC a t b f := rfl

/-- This is the classical operator-norm estimate invoked in the first paragraph of the proof of
Lemma 2.2. -/
theorem norm_convectiveHeatOperator_le (a t : ℝ) (b : E) :
    ‖convectiveHeatOperator (F := F) a t b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_convectiveHeatFlowBUC_le a t b f

@[simp]
theorem convectiveHeatOperator_zero (a : ℝ) (b : E) :
    convectiveHeatOperator (F := F) a 0 b = ContinuousLinearMap.id ℝ (BUC E F) := by
  ext f
  simp

/-- Heat flow commutes with spatial translation. -/
theorem heatFlowBUC_translate (a t : ℝ) (b : E) (f : BUC E F) :
    heatFlowBUC a t (BUC.translate b f) = BUC.translate b (heatFlowBUC a t f) := by
  ext x
  change (∫ z, f ((x + heatScale a t • z) - b) ∂(stdGaussian E)) =
    ∫ z, f ((x - b) + heatScale a t • z) ∂(stdGaussian E)
  congr 1
  funext z
  congr 1
  abel

/-- Strong continuity in time of convective heat flow. -/
theorem continuous_convectiveHeatFlowBUC_time (a : ℝ) (b : E) (f : BUC E F) :
    Continuous fun t ↦ convectiveHeatFlowBUC a t b f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hheat : ContinuousAt (fun t ↦ heatFlowBUC a t f) t₀ :=
    (continuous_heatFlowBUC_time a f).continuousAt
  have hshift : ContinuousAt
      (fun t ↦ BUC.translate (-(t • b)) (heatFlowBUC a t₀ f)) t₀ := by
    have hparam : ContinuousAt (fun t : ℝ ↦ -(t • b)) t₀ := by fun_prop
    simpa [Function.comp_def] using
      (BUC.continuous_translate (heatFlowBUC a t₀ f)).continuousAt.comp hparam
  obtain ⟨δ₁, hδ₁, hheatδ⟩ :=
    Metric.continuousAt_iff.mp hheat (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, hshiftδ⟩ :=
    Metric.continuousAt_iff.mp hshift (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ht
  have ht₁ : dist t t₀ < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : dist t t₀ < δ₂ := lt_of_lt_of_le ht (min_le_right _ _)
  calc
    dist (convectiveHeatFlowBUC a t b f) (convectiveHeatFlowBUC a t₀ b f) ≤
        dist (BUC.translate (-(t • b)) (heatFlowBUC a t f))
            (BUC.translate (-(t • b)) (heatFlowBUC a t₀ f)) +
          dist (BUC.translate (-(t • b)) (heatFlowBUC a t₀ f))
            (BUC.translate (-(t₀ • b)) (heatFlowBUC a t₀ f)) := by
      simpa [convectiveHeatFlowBUC] using
        dist_triangle (BUC.translate (-(t • b)) (heatFlowBUC a t f))
          (BUC.translate (-(t • b)) (heatFlowBUC a t₀ f))
          (BUC.translate (-(t₀ • b)) (heatFlowBUC a t₀ f))
    _ = dist (heatFlowBUC a t f) (heatFlowBUC a t₀ f) +
          dist (BUC.translate (-(t • b)) (heatFlowBUC a t₀ f))
            (BUC.translate (-(t₀ • b)) (heatFlowBUC a t₀ f)) := by
      rw [dist_translate_eq]
    _ < ε / 2 + ε / 2 := add_lt_add (hheatδ ht₁) (hshiftδ ht₂)
    _ = ε := by ring

/-- Semigroup law for convective heat evolution. -/
theorem convectiveHeatOperator_add_time {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (b : E) :
    (convectiveHeatOperator (F := F) a s b).comp (convectiveHeatOperator a t b) =
      convectiveHeatOperator a (s + t) b := by
  apply ContinuousLinearMap.ext
  intro f
  change BUC.translate (-(s • b))
      (heatFlowBUC a s (BUC.translate (-(t • b)) (heatFlowBUC a t f))) =
    BUC.translate (-((s + t) • b)) (heatFlowBUC a (s + t) f)
  rw [heatFlowBUC_translate, BUC.translate_add]
  have hheat := congrArg (fun L ↦ L f)
    (heatOperator_add_time (E := E) (F := F) ha hs ht)
  change heatFlowBUC a s (heatFlowBUC a t f) = heatFlowBUC a (s + t) f at hheat
  rw [hheat]
  congr 1
  module

/-- Convective heat flow as a strongly continuous semigroup. -/
def convectiveHeatC0Semigroup (a : ℝ) (ha : 0 ≤ a) (b : E) :
    C0Semigroup ℝ (BUC E F) where
  toFun t := convectiveHeatOperator a t b
  map_zero' := convectiveHeatOperator_zero a b
  map_add' s t := by
    simpa using (convectiveHeatOperator_add_time (E := E) (F := F) ha s.2 t.2 b).symm
  strongContinuous' f := by
    exact (continuous_convectiveHeatFlowBUC_time a b f).comp continuous_subtype_val

@[simp]
theorem convectiveHeatC0Semigroup_apply (a : ℝ) (ha : 0 ≤ a) (b : E)
    (t : NNReal) (f : BUC E F) :
    convectiveHeatC0Semigroup a ha b t f = convectiveHeatFlowBUC a t b f := rfl

/-- The convective heat evolution is a strongly continuous contraction semigroup. -/
def convectiveHeatContractionSemigroup (a : ℝ) (ha : 0 ≤ a) (b : E) :
    ContractionSemigroup ℝ (BUC E F) :=
  ContractionSemigroup.ofNormApplyLE (convectiveHeatC0Semigroup a ha b)
    (fun t f ↦ norm_convectiveHeatFlowBUC_le a t b f)

@[simp]
theorem convectiveHeatContractionSemigroup_apply (a : ℝ) (ha : 0 ≤ a) (b : E)
    (t : NNReal) (f : BUC E F) :
    convectiveHeatContractionSemigroup a ha b t f = convectiveHeatFlowBUC a t b f := rfl

end ConvectiveHeat

section ComplexConvectiveHeat

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Complex linearity of convective heat flow. -/
theorem convectiveHeatFlowBUC_smul_complex
    (a t : ℝ) (b : E) (r : ℂ) (f : BUC E ℂ) :
    convectiveHeatFlowBUC a t b (r • f) = r • convectiveHeatFlowBUC a t b f := by
  ext x
  rw [convectiveHeatFlowBUC_apply, BUC.smul_apply, convectiveHeatFlowBUC_apply]
  unfold heatFlow
  simp_rw [BUC.smul_apply, smul_eq_mul]
  exact MeasureTheory.integral_const_mul r _

/-- Complex-linear convective heat evolution. -/
def complexConvectiveHeatOperator (a t : ℝ) (b : E) :
    BUC E ℂ →L[ℂ] BUC E ℂ :=
  LinearMap.mkContinuous
    { toFun := convectiveHeatFlowBUC a t b
      map_add' := convectiveHeatFlowBUC_add a t b
      map_smul' := fun r f ↦ convectiveHeatFlowBUC_smul_complex a t b r f }
    1 (fun f ↦ by simpa using norm_convectiveHeatFlowBUC_le a t b f)

@[simp]
theorem complexConvectiveHeatOperator_apply (a t : ℝ) (b : E) (f : BUC E ℂ) :
    complexConvectiveHeatOperator a t b f = convectiveHeatFlowBUC a t b f := rfl

theorem norm_complexConvectiveHeatOperator_le (a t : ℝ) (b : E) :
    ‖complexConvectiveHeatOperator a t b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_convectiveHeatFlowBUC_le a t b f

@[simp]
theorem complexConvectiveHeatOperator_zero (a : ℝ) (b : E) :
    complexConvectiveHeatOperator a 0 b = ContinuousLinearMap.id ℂ (BUC E ℂ) := by
  ext f
  simp

/-- Semigroup law for the complex-linear realization. -/
theorem complexConvectiveHeatOperator_add_time {a s t : ℝ} (ha : 0 ≤ a)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (b : E) :
    (complexConvectiveHeatOperator a s b).comp (complexConvectiveHeatOperator a t b) =
      complexConvectiveHeatOperator a (s + t) b := by
  apply ContinuousLinearMap.ext
  intro f
  change BUC.translate (-(s • b))
      (heatFlowBUC a s (BUC.translate (-(t • b)) (heatFlowBUC a t f))) =
    BUC.translate (-((s + t) • b)) (heatFlowBUC a (s + t) f)
  rw [heatFlowBUC_translate, BUC.translate_add]
  have hheat := congrArg (fun L ↦ L f)
    (heatOperator_add_time (E := E) (F := ℂ) ha hs ht)
  change heatFlowBUC a s (heatFlowBUC a t f) = heatFlowBUC a (s + t) f at hheat
  rw [hheat]
  congr 1
  module

/-- Complex-linear convective heat flow as a strongly continuous semigroup. -/
def complexConvectiveHeatC0Semigroup (a : ℝ) (ha : 0 ≤ a) (b : E) :
    C0Semigroup ℂ (BUC E ℂ) where
  toFun t := complexConvectiveHeatOperator a t b
  map_zero' := complexConvectiveHeatOperator_zero a b
  map_add' s t := by
    simpa using
      (complexConvectiveHeatOperator_add_time (E := E) ha s.2 t.2 b).symm
  strongContinuous' f := by
    exact (continuous_convectiveHeatFlowBUC_time a b f).comp continuous_subtype_val

@[simp]
theorem complexConvectiveHeatC0Semigroup_apply (a : ℝ) (ha : 0 ≤ a) (b : E)
    (t : NNReal) (f : BUC E ℂ) :
    complexConvectiveHeatC0Semigroup a ha b t f = convectiveHeatFlowBUC a t b f := rfl

/-- The complex-linear convective heat evolution is a contraction semigroup. -/
def complexConvectiveHeatContractionSemigroup (a : ℝ) (ha : 0 ≤ a) (b : E) :
    ContractionSemigroup ℂ (BUC E ℂ) :=
  ContractionSemigroup.ofNormApplyLE (complexConvectiveHeatC0Semigroup a ha b)
    (fun t f ↦ norm_convectiveHeatFlowBUC_le a t b f)

end ComplexConvectiveHeat

end

end Planarwave
