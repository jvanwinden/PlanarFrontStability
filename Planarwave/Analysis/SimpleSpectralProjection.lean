/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Planarwave.Analysis.SimpleEigenvaluePerturbation
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

/-!
# The local spectral projection of a simple Fredholm eigenvalue

This file supplies the analytic-perturbation part of Proposition 2.1 in the planar-wave paper.
The Lyapunov--Schmidt eigenpair and its Taylor coefficient are constructed in
`SimpleEigenvaluePerturbation`.  Here we study the full affine pencil

`A(q) - z i = A₀ - q B - z i`

on the fixed graph-norm domain.  The first step is the standard stability argument for the
invertible Fredholm-complement block.  It will be used to construct the perturbed left
eigenfunctional, prove local spectral uniqueness, and identify the resulting rank-one map with
the spectral projection.
-/

open Function Filter
open scoped Topology ContDiff

universe u v

noncomputable section

namespace Planarwave
namespace SimpleFredholmZeroMode

variable {X : Type u} {Dom : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

variable (S : SimpleFredholmZeroMode X Dom)

/-! ## Stability of the complementary resolvent block -/

/-- The common-domain affine pencil `A₀ - qB - z i`. -/
def affinePencil (B : Dom →L[ℂ] X) (q z : ℂ) : Dom →L[ℂ] X :=
  S.operator - q • B - z • S.inclusion

@[simp]
theorem affinePencil_apply (B : Dom →L[ℂ] X) (q z : ℂ) (x : Dom) :
    S.affinePencil B q z x = S.operator x - q • B x - z • S.inclusion x :=
  rfl

@[simp]
theorem affinePencil_zero_zero (B : Dom →L[ℂ] X) :
    S.affinePencil B 0 0 = S.operator := by
  simp [affinePencil]

/-- The lower-right Fredholm block: restrict the pencil to the fixed domain complement and
project its values onto the ambient complement. -/
def complementPencil (B : Dom →L[ℂ] X) (q z : ℂ) :
    S.domainComplement →L[ℂ] S.ambientComplement :=
  S.complementProjection.comp
    ((S.affinePencil B q z).comp S.domainComplement.subtypeL)

@[simp]
theorem complementPencil_apply_coe (B : Dom →L[ℂ] X) (q z : ℂ)
    (x : S.domainComplement) :
    (S.complementPencil B q z x : X) =
      S.affinePencil B q z (x : Dom) -
        S.projection (S.affinePencil B q z (x : Dom)) :=
  rfl

@[simp]
theorem complementPencil_zero_zero (B : Dom →L[ℂ] X) :
    S.complementPencil B 0 0 = S.complementOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp [complementPencil, S.functional_operator]

/-- The complementary block depends continuously on both the perturbation parameter and the
spectral parameter. -/
theorem continuous_complementPencil (B : Dom →L[ℂ] X) :
    Continuous (fun p : ℂ × ℂ ↦ S.complementPencil B p.1 p.2) := by
  unfold complementPencil affinePencil
  fun_prop

/-- Invertibility of the Fredholm-complement block persists for `(q,z)` near `(0,0)`.  This is
the fixed-domain form of the openness-of-the-resolvent argument used in analytic perturbation
theory. -/
theorem eventually_complementPencil_isInvertible (B : Dom →L[ℂ] X) :
    ∀ᶠ p in nhds (0, 0), (S.complementPencil B p.1 p.2).IsInvertible := by
  let U : Set (S.domainComplement →L[ℂ] S.ambientComplement) :=
    Set.range ((↑) :
      (S.domainComplement ≃L[ℂ] S.ambientComplement) →
        S.domainComplement →L[ℂ] S.ambientComplement)
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen
  have hzero : S.complementPencil B 0 0 ∈ U := by
    refine ⟨S.complementOperatorEquiv, ?_⟩
    exact (S.complementPencil_zero_zero B).symm
  have hpreimage :
      (fun p : ℂ × ℂ ↦ S.complementPencil B p.1 p.2) ⁻¹' U ∈ nhds (0, 0) :=
    (S.continuous_complementPencil B).continuousAt (hU.mem_nhds hzero)
  filter_upwards [hpreimage] with p hp
  exact hp

/-! ## The complementary block along the critical branch -/

/-- The pencil evaluated on the Lyapunov--Schmidt critical eigenvalue. -/
def criticalPencil (B : Dom →L[ℂ] X) (q : ℂ) : Dom →L[ℂ] X :=
  S.affinePencil B q (S.eigenvalueBranch B q)

/-- The complementary block evaluated on the critical eigenvalue. -/
def criticalComplementPencil (B : Dom →L[ℂ] X) (q : ℂ) :
    S.domainComplement →L[ℂ] S.ambientComplement :=
  S.complementProjection.comp
    ((S.criticalPencil B q).comp S.domainComplement.subtypeL)

@[simp]
theorem criticalPencil_zero (B : Dom →L[ℂ] X) :
    S.criticalPencil B 0 = S.operator := by
  simp [criticalPencil]

@[simp]
theorem criticalComplementPencil_zero (B : Dom →L[ℂ] X) :
    S.criticalComplementPencil B 0 = S.complementOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp [criticalComplementPencil, S.functional_operator]

/-- Along the critical branch the complementary block remains invertible near the origin. -/
theorem eventually_criticalComplementPencil_isInvertible (B : Dom →L[ℂ] X) :
    ∀ᶠ q in nhds 0, (S.criticalComplementPencil B q).IsInvertible := by
  have hpair :
      Tendsto (fun q : ℂ ↦ (q, S.eigenvalueBranch B q)) (nhds 0) (nhds (0, 0)) := by
    have hlambda : ContinuousAt (S.eigenvalueBranch B) 0 :=
      (S.hasDerivAt_eigenvalueBranch B).continuousAt
    have hpair' :
        Tendsto (fun q : ℂ ↦ (q, S.eigenvalueBranch B q)) (nhds 0)
          (nhds ((0 : ℂ), S.eigenvalueBranch B 0)) :=
      continuousAt_id.prodMk hlambda
    simpa only [S.eigenvalueBranch_zero] using hpair'
  exact hpair.eventually (S.eventually_complementPencil_isInvertible B)

/-- The constructed eigenvector is killed by the critical pencil near zero. -/
theorem eventually_criticalPencil_eigenvector_eq_zero (B : Dom →L[ℂ] X) :
    ∀ᶠ q in nhds 0,
      S.criticalPencil B q (S.eigenvectorBranch B q) = 0 := by
  filter_upwards [S.eventually_eigenvalue_equation B] with q hq
  simpa [criticalPencil, affinePencil, sub_eq_zero] using hq

/-- The inverse of the complementary block, defined globally by Mathlib's total inverse and
equal to the genuine bounded inverse wherever the block is invertible. -/
def criticalComplementInverse (B : Dom →L[ℂ] X) (q : ℂ) :
    S.ambientComplement →L[ℂ] S.domainComplement :=
  (S.criticalComplementPencil B q).inverse

/-- The unique domain-complement vector whose complementary critical-pencil image agrees with
the complementary part of `w`, whenever the complementary block is invertible. -/
def criticalComplementSolution (B : Dom →L[ℂ] X) (q : ℂ) :
    X →L[ℂ] S.domainComplement :=
  (S.criticalComplementInverse B q).comp S.complementProjection

/-- The perturbed left eigenfunctional.  It removes from `w` the unique domain-complement
component having the same complementary image under the critical pencil, then reads off the
remaining neutral coefficient with `ℓ`. -/
def criticalCokernelFunctional (B : Dom →L[ℂ] X) (q : ℂ) : X →L[ℂ] ℂ :=
  S.functional -
    (S.functional.comp (S.criticalPencil B q)).comp
      (S.domainComplement.subtypeL.comp
        (S.criticalComplementSolution B q))

@[simp]
theorem criticalCokernelFunctional_apply (B : Dom →L[ℂ] X) (q : ℂ) (w : X) :
    S.criticalCokernelFunctional B q w =
      S.functional w - S.functional
        (S.criticalPencil B q
          ((S.criticalComplementSolution B q w :
            S.domainComplement) : Dom)) :=
  rfl

@[simp]
theorem criticalCokernelFunctional_zero (B : Dom →L[ℂ] X) :
    S.criticalCokernelFunctional B 0 = S.functional := by
  apply ContinuousLinearMap.ext
  intro w
  simp [criticalCokernelFunctional, S.functional_operator]

/-- The complementary block at the origin is a continuous linear equivalence. -/
theorem criticalComplementPencil_zero_isInvertible (B : Dom →L[ℂ] X) :
    (S.criticalComplementPencil B 0).IsInvertible := by
  refine ⟨S.complementOperatorEquiv, ?_⟩
  exact (S.criticalComplementPencil_zero B).symm

/-- The implicit-function branch is holomorphic at the origin. -/
theorem contDiffAt_eigenpairBranch (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.eigenpairBranch B) 0 := by
  simpa only [eigenpairBranch] using
    (S.contDiff_eigenpairEquation B).contDiffAt.contDiffAt_implicitFunction
      (by simp) (S.eigenpairEquation_partialDerivative_isInvertible B)

/-- The critical eigenvalue branch is holomorphic at the origin. -/
theorem contDiffAt_eigenvalueBranch (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.eigenvalueBranch B) 0 := by
  have hbranch := S.contDiffAt_eigenpairBranch B
  unfold eigenvalueBranch
  fun_prop

/-- Holomorphic dependence of the critical pencil at the origin. -/
theorem contDiffAt_criticalPencil (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalPencil B) 0 := by
  have hlambda := S.contDiffAt_eigenvalueBranch B
  unfold criticalPencil affinePencil
  fun_prop

/-- Holomorphic dependence of the complementary critical block at the origin. -/
theorem contDiffAt_criticalComplementPencil (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalComplementPencil B) 0 := by
  have hcritical := S.contDiffAt_criticalPencil B
  unfold criticalComplementPencil
  fun_prop

/-- The total inverse of the complementary block is holomorphic at the origin, where it is
the genuine inverse. -/
theorem contDiffAt_criticalComplementInverse (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalComplementInverse B) 0 := by
  unfold criticalComplementInverse
  have hinverse : ContDiffAt ℂ ω ContinuousLinearMap.inverse
        (S.criticalComplementPencil B 0) :=
    (S.criticalComplementPencil_zero_isInvertible B).contDiffAt_map_inverse
  have hcomp := hinverse.comp 0 (S.contDiffAt_criticalComplementPencil B)
  exact hcomp.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)

/-- Holomorphic dependence of the complementary solution operator. -/
theorem contDiffAt_criticalComplementSolution (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalComplementSolution B) 0 := by
  have hinverse := S.contDiffAt_criticalComplementInverse B
  unfold criticalComplementSolution
  fun_prop

/-- Holomorphic dependence of the perturbed left eigenfunctional. -/
theorem contDiffAt_criticalCokernelFunctional (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalCokernelFunctional B) 0 := by
  have hpencil := S.contDiffAt_criticalPencil B
  have hsolution := S.contDiffAt_criticalComplementSolution B
  unfold criticalCokernelFunctional
  fun_prop

/-- Holomorphic dependence of the normalized right eigenvector in the graph domain. -/
theorem contDiffAt_eigenvectorBranch (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.eigenvectorBranch B) 0 := by
  have hbranch := S.contDiffAt_eigenpairBranch B
  have hcorrection :
      ContDiffAt ℂ ω
        (fun q ↦ ((S.eigenpairBranch B q).2 : S.domainComplement)) 0 :=
    contDiffAt_snd.comp 0 hbranch
  have hcoe : ContDiffAt ℂ ω
      (fun q ↦ ((S.eigenpairBranch B q).2 : Dom)) 0 :=
    S.domainComplement.subtypeL.contDiff.contDiffAt.comp 0 hcorrection
  exact contDiffAt_const.add hcoe

/-- Holomorphic dependence of the embedded normalized right eigenvector. -/
theorem contDiffAt_inclusion_eigenvectorBranch (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (fun q ↦ S.inclusion (S.eigenvectorBranch B q)) 0 :=
  S.inclusion.contDiff.contDiffAt.comp 0 (S.contDiffAt_eigenvectorBranch B)

/-- Remove the normalized neutral coordinate of a graph-domain vector. -/
def domainComplementPart (x : Dom) : S.domainComplement :=
  ⟨x - S.functional (S.inclusion x) • S.mode, by
    change S.functional
      (S.inclusion (x - S.functional (S.inclusion x) • S.mode)) = 0
    simp [S.normalized]⟩

@[simp]
theorem domainComplementPart_coe (x : Dom) :
    (S.domainComplementPart x : Dom) =
      x - S.functional (S.inclusion x) • S.mode :=
  rfl

/-- Domain decomposition into the normalized neutral mode and the fixed complement. -/
theorem domain_eq_neutral_add_complement (x : Dom) :
    x = S.functional (S.inclusion x) • S.mode + S.domainComplementPart x := by
  simp [domainComplementPart]

/-- The inverse complementary block solves the projected resolvent equation. -/
theorem complementPencil_criticalComplementSolution
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible) (w : X) :
    S.criticalComplementPencil B q (S.criticalComplementSolution B q w) =
      S.complementProjection w := by
  exact hC.self_apply_inverse (S.complementProjection w)

/-- Resolvent decomposition associated with the perturbed cokernel functional. -/
theorem eq_cokernel_smul_mode_add_criticalPencil_solution
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible) (w : X) :
    w = S.criticalCokernelFunctional B q w • S.inclusion S.mode +
      S.criticalPencil B q
        ((S.criticalComplementSolution B q w : S.domainComplement) : Dom) := by
  let u : S.domainComplement := S.criticalComplementSolution B q w
  let r : X := w - S.criticalPencil B q (u : Dom)
  have hcomp : S.complementProjection r = 0 := by
    rw [show r = w - S.criticalPencil B q (u : Dom) by rfl, map_sub]
    change S.complementProjection w - S.criticalComplementPencil B q u = 0
    rw [S.complementPencil_criticalComplementSolution B q hC w, sub_self]
  have hr : r = S.projection r := by
    have hval := congrArg Subtype.val hcomp
    change r - S.projection r = 0 at hval
    exact sub_eq_zero.mp hval
  have hphase : S.functional r = S.criticalCokernelFunctional B q w := by
    simp [r, u, criticalCokernelFunctional_apply]
  have hr' :
      w - S.criticalPencil B q (u : Dom) =
        S.criticalCokernelFunctional B q w • S.inclusion S.mode := by
    calc
      w - S.criticalPencil B q (u : Dom) = r := rfl
      _ = S.projection r := hr
      _ = S.functional r • S.inclusion S.mode := S.projection_apply r
      _ = S.criticalCokernelFunctional B q w • S.inclusion S.mode := by rw [hphase]
  exact (sub_eq_iff_eq_add).mp hr'

/-- The complementary solution of a critical-pencil value is its fixed-complement domain
coordinate, corrected by the perturbed eigenvector coordinate. -/
theorem criticalComplementSolution_criticalPencil
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible)
    (heig : S.criticalPencil B q (S.eigenvectorBranch B q) = 0)
    (x : Dom) :
    S.criticalComplementSolution B q (S.criticalPencil B q x) =
      S.domainComplementPart x -
        S.functional (S.inclusion x) • (S.eigenpairBranch B q).2 := by
  let a : ℂ := S.functional (S.inclusion x)
  let x₀ : S.domainComplement := S.domainComplementPart x
  let u : S.domainComplement := (S.eigenpairBranch B q).2
  have heig' : S.criticalPencil B q (S.mode + (u : Dom)) = 0 := by
    simpa [u, eigenvectorBranch] using heig
  have hmode : S.criticalPencil B q S.mode = -S.criticalPencil B q (u : Dom) := by
    have hsum :
        S.criticalPencil B q S.mode + S.criticalPencil B q (u : Dom) = 0 := by
      simpa only [map_add] using heig'
    exact eq_neg_of_add_eq_zero_left hsum
  have hx : x = a • S.mode + (x₀ : Dom) := by
    simpa [a, x₀] using S.domain_eq_neutral_add_complement x
  have hpencil :
      S.criticalPencil B q x =
        S.criticalPencil B q ((x₀ - a • u : S.domainComplement) : Dom) := by
    rw [hx]
    simp only [map_add, map_smul, Submodule.coe_sub, Submodule.coe_smul, map_sub]
    rw [hmode]
    module
  apply hC.injective
  rw [S.complementPencil_criticalComplementSolution B q hC]
  change S.complementProjection (S.criticalPencil B q x) =
    S.complementProjection
      (S.criticalPencil B q ((x₀ - a • u : S.domainComplement) : Dom))
  rw [hpencil]

/-- The perturbed cokernel functional annihilates the range of the critical pencil. -/
theorem criticalCokernelFunctional_criticalPencil
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible)
    (heig : S.criticalPencil B q (S.eigenvectorBranch B q) = 0)
    (x : Dom) :
    S.criticalCokernelFunctional B q (S.criticalPencil B q x) = 0 := by
  rw [S.criticalCokernelFunctional_apply]
  rw [S.criticalComplementSolution_criticalPencil B q hC heig x]
  let a : ℂ := S.functional (S.inclusion x)
  let x₀ : S.domainComplement := S.domainComplementPart x
  let u : S.domainComplement := (S.eigenpairBranch B q).2
  have heig' : S.criticalPencil B q (S.mode + (u : Dom)) = 0 := by
    simpa [u, eigenvectorBranch] using heig
  have hmode : S.criticalPencil B q S.mode = -S.criticalPencil B q (u : Dom) := by
    have hsum :
        S.criticalPencil B q S.mode + S.criticalPencil B q (u : Dom) = 0 := by
      simpa only [map_add] using heig'
    exact eq_neg_of_add_eq_zero_left hsum
  have hx : x = a • S.mode + (x₀ : Dom) := by
    simpa [a, x₀] using S.domain_eq_neutral_add_complement x
  have hpencil :
      S.criticalPencil B q x =
        S.criticalPencil B q ((x₀ - a • u : S.domainComplement) : Dom) := by
    rw [hx]
    simp only [map_add, map_smul, Submodule.coe_sub, Submodule.coe_smul, map_sub]
    rw [hmode]
    module
  rw [hpencil, sub_self]

/-- Near zero, the critical pencil has the exact perturbed Fredholm alternative: its range is
the kernel of the perturbed left eigenfunctional. -/
theorem eventually_range_criticalPencil_eq_kernel_criticalCokernelFunctional
    (B : Dom →L[ℂ] X) :
    ∀ᶠ q in nhds 0,
      LinearMap.range (S.criticalPencil B q).toLinearMap =
        LinearMap.ker (S.criticalCokernelFunctional B q).toLinearMap := by
  filter_upwards [S.eventually_criticalComplementPencil_isInvertible B,
    S.eventually_criticalPencil_eigenvector_eq_zero B] with q hC heig
  ext w
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    exact S.criticalCokernelFunctional_criticalPencil B q hC heig x
  · intro hw
    change S.criticalCokernelFunctional B q w = 0 at hw
    let u : S.domainComplement := S.criticalComplementSolution B q w
    refine ⟨(u : Dom), ?_⟩
    have hdecomp := S.eq_cokernel_smul_mode_add_criticalPencil_solution B q hC w
    rw [hw, zero_smul, zero_add] at hdecomp
    exact hdecomp.symm

/-! ## The normalized perturbed projection -/

/-- The pairing of the unnormalized perturbed left functional with the normalized right
eigenvector. -/
def criticalNormalization (B : Dom →L[ℂ] X) (q : ℂ) : ℂ :=
  S.criticalCokernelFunctional B q
    (S.inclusion (S.eigenvectorBranch B q))

@[simp]
theorem criticalNormalization_zero (B : Dom →L[ℂ] X) :
    S.criticalNormalization B 0 = 1 := by
  simp [criticalNormalization, S.normalized]

/-- The critical normalization varies holomorphically. -/
theorem contDiffAt_criticalNormalization (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalNormalization B) 0 := by
  have hfunctional := S.contDiffAt_criticalCokernelFunctional B
  have hvector := S.contDiffAt_inclusion_eigenvectorBranch B
  exact hfunctional.clm_apply hvector

/-- The perturbed left/right pairing remains nonzero near the origin. -/
theorem eventually_criticalNormalization_ne_zero (B : Dom →L[ℂ] X) :
    ∀ᶠ q in nhds 0, S.criticalNormalization B q ≠ 0 := by
  exact (S.contDiffAt_criticalNormalization B).continuousAt.eventually_ne (by simp)

/-- The perturbed left eigenfunctional normalized against the right eigenvector. -/
def criticalLeftFunctional (B : Dom →L[ℂ] X) (q : ℂ) : X →L[ℂ] ℂ :=
  (S.criticalNormalization B q)⁻¹ • S.criticalCokernelFunctional B q

@[simp]
theorem criticalLeftFunctional_zero (B : Dom →L[ℂ] X) :
    S.criticalLeftFunctional B 0 = S.functional := by
  simp [criticalLeftFunctional]

/-- The normalized left eigenfunctional depends holomorphically on the perturbation parameter. -/
theorem contDiffAt_criticalLeftFunctional (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalLeftFunctional B) 0 := by
  have hnormalization := S.contDiffAt_criticalNormalization B
  have hfunctional := S.contDiffAt_criticalCokernelFunctional B
  have hne : S.criticalNormalization B 0 ≠ 0 := by simp
  exact (hnormalization.inv hne).smul hfunctional

/-- The normalized perturbed rank-one projection.  The range/kernel results below characterize
it as the spectral projection associated with the locally simple critical eigenvalue. -/
def criticalProjection (B : Dom →L[ℂ] X) (q : ℂ) : X →L[ℂ] X :=
  (S.criticalLeftFunctional B q).smulRight
    (S.inclusion (S.eigenvectorBranch B q))

@[simp]
theorem criticalProjection_apply (B : Dom →L[ℂ] X) (q : ℂ) (w : X) :
    S.criticalProjection B q w =
      S.criticalLeftFunctional B q w •
        S.inclusion (S.eigenvectorBranch B q) :=
  rfl

@[simp]
theorem criticalProjection_zero (B : Dom →L[ℂ] X) :
    S.criticalProjection B 0 = S.projection := by
  ext w
  simp [criticalProjection, projection_apply]

/-- The normalized critical projection depends holomorphically on the perturbation parameter. -/
theorem contDiffAt_criticalProjection (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.criticalProjection B) 0 := by
  exact (S.contDiffAt_criticalLeftFunctional B).smulRight
    (S.contDiffAt_inclusion_eigenvectorBranch B)

/-- Exact normalization of the perturbed left and right modes whenever their pairing is nonzero. -/
theorem criticalLeftFunctional_eigenvector
    (B : Dom →L[ℂ] X) (q : ℂ) (hq : S.criticalNormalization B q ≠ 0) :
    S.criticalLeftFunctional B q (S.inclusion (S.eigenvectorBranch B q)) = 1 := by
  change (S.criticalNormalization B q)⁻¹ * S.criticalNormalization B q = 1
  exact inv_mul_cancel₀ hq

/-- The critical rank-one map is a projection near zero. -/
theorem eventually_criticalProjection_idempotent (B : Dom →L[ℂ] X) :
    ∀ᶠ q in nhds 0, ∀ w : X,
      S.criticalProjection B q (S.criticalProjection B q w) =
        S.criticalProjection B q w := by
  filter_upwards [S.eventually_criticalNormalization_ne_zero B] with q hq
  intro w
  simp [criticalProjection_apply, S.criticalLeftFunctional_eigenvector B q hq]

/-- The actual perturbed projection has the operator-norm estimate `P(q)-P(0)=O(q)`. -/
theorem criticalProjection_sub_projection_isBigO (B : Dom →L[ℂ] X) :
    (fun q ↦ S.criticalProjection B q - S.projection) =O[nhds 0]
      fun q : ℂ ↦ q := by
  have h := ((S.contDiffAt_criticalProjection B).differentiableAt (by simp)).hasFDerivAt.isBigO_sub
  simpa only [S.criticalProjection_zero, sub_zero] using h

end SimpleFredholmZeroMode
end Planarwave
