/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Statement
import all Planarwave.Analysis.FrontCoefficient
import all Planarwave.Analysis.DiffusionEigenbasis
import Planarwave.Analysis.ConvectiveHeatGenerator
import Planarwave.Analysis.SemigroupGenerator

/-!
# The concrete principal longitudinal diffusion semigroup

In the proof of Lemma 2.2, the operator `D ∂zz + c ∂z - q D` is diagonalized by the real
diffusion eigenbasis and then complexified. Here this construction gives the actual semigroup
on `BUC ℝ (ℂ^n)`, a Gaussian bound uniform over nonnegative `q`, and the right generator limit
on the common `ComplexBUC2` domain. Positive-time smoothing and the closedness of the generator
graph show that this common domain is a core. Full domain equality is not asserted here.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} [Nontrivial (ℝ^n)]

/-- The principal longitudinal evolution, extended to real time for differentiation. Its
semigroup interpretation is only used at nonnegative times. -/
def frontDiffusionFlowBUC (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q t : ℝ) (v : BUC ℝ (ℂ^n)) : BUC ℝ (ℂ^n) :=
  diffusionBUCCoordinatesEquiv D hD (fun i ↦
    (Real.exp ((-q * diffusionEigenvalues D hD i) * t) : ℂ) •
      convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t c
        ((diffusionBUCCoordinatesEquiv D hD).symm v i))

/-- The principal part of the Fourier symbol as a strongly continuous complex-linear
semigroup, using the concrete diffusion eigenbasis. -/
def frontDiffusionC0Semigroup (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (c q : ℝ) :
    C0Semigroup ℂ (BUC ℝ (ℂ^n)) :=
  conjugatedDiagonalDiffusionC0Semigroup (diffusionEigenvalues D hD)
    (diffusionEigenvalues_nonneg D hD) c q (diffusionBUCCoordinatesEquiv D hD)

@[simp]
theorem frontDiffusionC0Semigroup_apply (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q : ℝ) (t : NNReal) (v : BUC ℝ (ℂ^n)) :
    frontDiffusionC0Semigroup D hD c q t v = frontDiffusionFlowBUC D hD c q t v := rfl

@[simp]
theorem frontDiffusionFlowBUC_zero (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q : ℝ) (v : BUC ℝ (ℂ^n)) : frontDiffusionFlowBUC D hD c q 0 v = v := by
  simpa only [frontDiffusionC0Semigroup_apply, NNReal.coe_zero] using
    (frontDiffusionC0Semigroup D hD c q).zero_apply v

/-- The constants are chosen before the frequency and time variables: this is the uniform
Gaussian estimate immediately preceding (2.3) in the paper. -/
theorem exists_uniform_frontDiffusion_bound
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) :
    ∃ M > 0, ∃ μ > 0, ∀ c q : ℝ, 0 ≤ q → ∀ t : NNReal,
      ‖frontDiffusionC0Semigroup D hD c q t‖ ≤ M * Real.exp (-μ * q * (t : ℝ)) := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  let J := diffusionBUCCoordinatesEquiv D hD
  let K := ‖J.toContinuousLinearMap‖ * ‖J.symm.toContinuousLinearMap‖
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), μ, hμ, ?_⟩
  intro c q hq t
  exact (norm_conjugatedDiagonalDiffusionC0Semigroup_le (diffusionEigenvalues D hD)
    (diffusionEigenvalues_nonneg D hD) c q μ hμle hq J t).trans
      (mul_le_mul_of_nonneg_right (le_max_left K 1) (Real.exp_pos _).le)

omit [Nontrivial (ℝ^n)] in
/-- Strong time continuity of the real-time expression used for the generator limit. -/
theorem continuous_frontDiffusionFlowBUC (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q : ℝ) (v : BUC ℝ (ℂ^n)) : Continuous fun t ↦ frontDiffusionFlowBUC D hD c q t v := by
  apply (diffusionBUCCoordinatesEquiv D hD).continuous.comp
  apply continuous_pi
  intro i
  exact (by fun_prop : Continuous fun t : ℝ ↦
    (Real.exp ((-q * diffusionEigenvalues D hD i) * t) : ℂ)).smul
      (continuous_convectiveHeatFlowBUC_time _ c _)

omit [Nontrivial (ℝ^n)] in
/-- The constant eigenbasis preserves spatial derivative identities. -/
theorem hasDerivAt_diffusionBUCCoordinatesEquiv
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (v w : Fin n → BUC ℝ ℂ)
    (hw : ∀ i x, HasDerivAt (v i) (w i x) x) (x : ℝ) :
    HasDerivAt (diffusionBUCCoordinatesEquiv D hD v)
      (diffusionBUCCoordinatesEquiv D hD w x) x := by
  let L := (diffusionCoordinatesEquiv D hD).toContinuousLinearMap.restrictScalars ℝ
  exact L.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_pi.mpr fun i ↦ hw i x)

omit [Nontrivial (ℝ^n)] in
/-- The inverse eigenbasis preserves spatial derivative identities as well. -/
theorem hasDerivAt_diffusionBUCCoordinatesEquiv_symm
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (v w : BUC ℝ (ℂ^n))
    (hw : ∀ x, HasDerivAt v (w x) x) (i : Fin n) (x : ℝ) :
    HasDerivAt ((diffusionBUCCoordinatesEquiv D hD).symm v i)
      ((diffusionBUCCoordinatesEquiv D hD).symm w i x) x := by
  let L : ℂ^n →L[ℂ] ℂ := (ContinuousLinearMap.proj i).comp
    (diffusionCoordinatesEquiv D hD).symm.toContinuousLinearMap
  exact (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x (hw x)

/-- Every positive-time orbit of the principal semigroup lies in the common `BUC²` domain. -/
theorem exists_complexBUC2_frontDiffusionFlowBUC
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℝ) {t : ℝ} (ht : 0 < t) (v : BUC ℝ (ℂ^n)) :
    ∃ w : ComplexBUC2 (ℂ^n), ComplexBUC2.value (ℂ^n) w =
      frontDiffusionFlowBUC D hD c q t v := by
  let J := diffusionBUCCoordinatesEquiv D hD
  let r (i : Fin n) : ℂ := Real.exp ((-q * diffusionEigenvalues D hD i) * t)
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  choose g h hg hh using fun i : Fin n ↦
    exists_buc_derivatives_convectiveHeatFlow (hμ.trans_le (hμle i)) ht c (J.symm v i)
  refine ⟨⟨((frontDiffusionFlowBUC D hD c q t v, J (fun i ↦ r i • g i)),
    J (fun i ↦ r i • h i)), ?_⟩, rfl⟩
  intro x
  constructor
  · exact hasDerivAt_diffusionBUCCoordinatesEquiv D hD _ _
      (fun i y ↦ (hg i y).const_smul (r i)) x
  · exact hasDerivAt_diffusionBUCCoordinatesEquiv D hD _ _
      (fun i y ↦ (hh i y).const_smul (r i)) x

omit [Nontrivial (ℝ^n)] in
/-- Spatial derivatives commute with the principal matrix evolution on differentiable BUC
data, by the same constant-eigenbasis calculation as in Lemma 2.2. -/
theorem hasDerivAt_frontDiffusionFlowBUC_space
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (c q t : ℝ)
    (v w : BUC ℝ (ℂ^n)) (hw : ∀ x, HasDerivAt v (w x) x) (x : ℝ) :
    HasDerivAt (frontDiffusionFlowBUC D hD c q t v)
      (frontDiffusionFlowBUC D hD c q t w x) x := by
  apply hasDerivAt_diffusionBUCCoordinatesEquiv
  intro i y
  exact (hasDerivAt_convectiveHeatFlow_space _ t c _ _
    (hasDerivAt_diffusionBUCCoordinatesEquiv_symm D hD v w hw i) y).const_smul
      (Real.exp ((-q * diffusionEigenvalues D hD i) * t) : ℂ)

/-- The principal evolution preserves the common domain, with derivatives evolved componentwise. -/
def frontDiffusionFlowBUC2 (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q t : ℝ) (v : ComplexBUC2 (ℂ^n)) : ComplexBUC2 (ℂ^n) :=
  ⟨((frontDiffusionFlowBUC D hD c q t (ComplexBUC2.value (ℂ^n) v),
      frontDiffusionFlowBUC D hD c q t (ComplexBUC2.deriv (ℂ^n) v)),
      frontDiffusionFlowBUC D hD c q t (ComplexBUC2.deriv2 (ℂ^n) v)), fun x ↦
    ⟨hasDerivAt_frontDiffusionFlowBUC_space D hD c q t _ _
        (ComplexBUC2.hasDerivAt_value (ℂ^n) v) x,
      hasDerivAt_frontDiffusionFlowBUC_space D hD c q t _ _
        (ComplexBUC2.hasDerivAt_deriv (ℂ^n) v) x⟩⟩

omit [Nontrivial (ℝ^n)] in
@[simp]
theorem frontDiffusionFlowBUC2_value (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q t : ℝ) (v : ComplexBUC2 (ℂ^n)) :
    ComplexBUC2.value (ℂ^n) (frontDiffusionFlowBUC2 D hD c q t v) =
      frontDiffusionFlowBUC D hD c q t (ComplexBUC2.value (ℂ^n) v) := rfl

omit [Nontrivial (ℝ^n)] in
/-- Transport of the diagonal differential expression to the common longitudinal domain. -/
theorem diffusion_generator_coordinates (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q : ℝ) (v : ComplexBUC2 (ℂ^n)) :
    diffusionBUCCoordinatesEquiv D hD (fun i ↦
      diffusionEigenvalues D hD i •
          ((diffusionBUCCoordinatesEquiv D hD).symm (ComplexBUC2.deriv2 (ℂ^n) v) i) +
        c • ((diffusionBUCCoordinatesEquiv D hD).symm (ComplexBUC2.deriv (ℂ^n) v) i) -
        (q * diffusionEigenvalues D hD i) •
          ((diffusionBUCCoordinatesEquiv D hD).symm (ComplexBUC2.value (ℂ^n) v) i)) =
      longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 v := by
  apply BUC.ext
  intro z
  let e := diffusionCoordinatesEquiv D hD
  have hDcoord (w : ℂ^n) : frontComplexifiedDiffusion D w =
      e (fun i ↦ (diffusionEigenvalues D hD i : ℂ) * e.symm w i) := by
    simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using
      complexifiedDiffusion_coordinates D hD (e.symm w)
  simp only [diffusionBUCCoordinatesEquiv_apply, BUC.sub_apply, BUC.add_apply,
    BUC.smul_apply, diffusionBUCCoordinatesEquiv_symm_apply, longitudinalOperator_apply,
    BUC.zero_apply, zero_apply, add_zero]
  change e _ = _
  rw [hDcoord, hDcoord]
  rw [show ComplexBUC2.deriv (ℂ^n) v z = e (e.symm (ComplexBUC2.deriv (ℂ^n) v z)) from
    (e.apply_symm_apply _).symm]
  rw [← e.map_smul, ← e.map_sub, ← e.map_smul, ← e.map_add]
  congr 1
  ext i
  simp [e, Complex.real_smul]
  ring

/-- The principal diffusion generator acts on `BUC²` as `D v'' + c v' - q D v`.
The derivative is in the BUC norm and is taken from nonnegative times. -/
theorem hasDerivWithinAt_frontDiffusionFlowBUC_zero
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℝ) (v : ComplexBUC2 (ℂ^n)) :
    HasDerivWithinAt
      (fun t ↦ frontDiffusionFlowBUC D hD c q t (ComplexBUC2.value (ℂ^n) v))
      (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 v)
      (Ici 0) 0 := by
  let J := diffusionBUCCoordinatesEquiv D hD
  let w₀ := J.symm (ComplexBUC2.value (ℂ^n) v)
  let w₁ := J.symm (ComplexBUC2.deriv (ℂ^n) v)
  let w₂ := J.symm (ComplexBUC2.deriv2 (ℂ^n) v)
  have hw₀ (i : Fin n) (x : ℝ) : HasDerivAt (w₀ i) (w₁ i x) x := by
    exact hasDerivAt_diffusionBUCCoordinatesEquiv_symm D hD _ _
      (ComplexBUC2.hasDerivAt_value (ℂ^n) v) i x
  have hw₁ (i : Fin n) (x : ℝ) : HasDerivAt (w₁ i) (w₂ i x) x := by
    exact hasDerivAt_diffusionBUCCoordinatesEquiv_symm D hD _ _
      (ComplexBUC2.hasDerivAt_deriv (ℂ^n) v) i x
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_diffusionEigenvalues D hD hDinj
  have hd : HasDerivWithinAt
      (fun t i ↦ (Real.exp ((-q * diffusionEigenvalues D hD i) * t) : ℂ) •
        convectiveHeatFlowBUC (diffusionEigenvalues D hD i) t c (w₀ i))
      (fun i ↦ diffusionEigenvalues D hD i • w₂ i + c • w₁ i -
        (q * diffusionEigenvalues D hD i) • w₀ i) (Ici 0) 0 := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using!
      hasDerivWithinAt_dampedConvectiveHeatFlowBUC_zero (hμ.trans_le (hμle i))
        c q (w₀ i) (w₁ i) (w₂ i) (hw₀ i) (hw₁ i)
  have h := (J.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hd
  change HasDerivWithinAt _ (J _) (Ici 0) 0 at h
  rw [diffusion_generator_coordinates D hD c q v] at h
  exact h

/-- The real-orbit convention for abstract semigroups agrees with the explicit flow at
nonnegative time. -/
theorem frontDiffusionC0Semigroup_realOrbit (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive)
    (c q : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : BUC ℝ (ℂ^n)) :
    (frontDiffusionC0Semigroup D hD c q).realOrbit v t =
      frontDiffusionFlowBUC D hD c q t v := by
  simp [C0Semigroup.realOrbit, Real.coe_toNNReal t ht]

/-- Every common-domain vector belongs to the generator domain of the constructed semigroup,
with the exact principal differential expression as its generator. -/
theorem frontDiffusionC0Semigroup_hasGeneratorAt
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℝ) (v : ComplexBUC2 (ℂ^n)) :
    (frontDiffusionC0Semigroup D hD c q).HasGeneratorAt (ComplexBUC2.value (ℂ^n) v)
      (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 v) := by
  apply (hasDerivWithinAt_frontDiffusionFlowBUC_zero D hD hDinj c q v).congr
  · intro t ht
    exact frontDiffusionC0Semigroup_realOrbit D hD c q ht _
  · simp

/-- The principal differential operator commutes with the constructed flow on `BUC²`. -/
theorem frontDiffusionFlowBUC_commute_generator
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : ComplexBUC2 (ℂ^n)) :
    frontDiffusionFlowBUC D hD c q t
        (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0 v) =
      longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0
        (frontDiffusionFlowBUC2 D hD c q t v) := by
  have h₁ := (frontDiffusionC0Semigroup_hasGeneratorAt D hD hDinj c q v).apply ⟨t, ht⟩
  have h₂ := frontDiffusionC0Semigroup_hasGeneratorAt D hD hDinj c q
    (frontDiffusionFlowBUC2 D hD c q t v)
  exact h₁.unique h₂

/-- The principal equation holds in the BUC norm at every positive time for common-domain data. -/
theorem hasDerivAt_frontDiffusionFlowBUC
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℝ) {t : ℝ} (ht : 0 < t) (v : ComplexBUC2 (ℂ^n)) :
    HasDerivAt (fun r ↦ frontDiffusionFlowBUC D hD c q r (ComplexBUC2.value (ℂ^n) v))
      (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0
        (frontDiffusionFlowBUC2 D hD c q t v)) t := by
  have h := (frontDiffusionC0Semigroup_hasGeneratorAt D hD hDinj c q v).hasDerivAt ht
  rw [frontDiffusionC0Semigroup_realOrbit D hD c q ht.le,
    frontDiffusionFlowBUC_commute_generator D hD hDinj c q ht.le] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  exact (frontDiffusionC0Semigroup_realOrbit D hD c q hr.le _).symm

/-- The `BUC²` principal differential operator is a core for the constructed semigroup:
its graph closure is exactly the full generator graph. No converse domain inclusion is
assumed in this statement. -/
theorem closure_frontDiffusionOperator_graph
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D)
    (c q : ℝ) :
    closure (range ((ComplexBUC2.valueCLM (ℂ^n)).prod
      (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0))) =
      {p : BUC ℝ (ℂ^n) × BUC ℝ (ℂ^n) |
        (frontDiffusionC0Semigroup D hD c q).HasGeneratorAt p.1 p.2} := by
  apply (frontDiffusionC0Semigroup D hD c q).closure_graph_eq_generatorGraph_of_smoothing
    (ComplexBUC2.value (ℂ^n))
    (longitudinalOperator (frontComplexifiedDiffusion D) (c : ℂ) (q : ℂ) 0)
    (frontDiffusionC0Semigroup_hasGeneratorAt D hD hDinj c q)
  intro t ht v
  exact exists_complexBUC2_frontDiffusionFlowBUC D hD hDinj c q ht v

end

end Planarwave
