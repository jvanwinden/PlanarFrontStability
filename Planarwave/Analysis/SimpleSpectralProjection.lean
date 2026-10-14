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

/-- The full affine pencil is holomorphic in `(q,z)`. -/
theorem contDiff_affinePencil (B : Dom →L[ℂ] X) :
    ContDiff ℂ ω (fun p : ℂ × ℂ ↦ S.affinePencil B p.1 p.2) := by
  unfold affinePencil
  fun_prop

/-- A compact set of resolvent points of the unperturbed pencil remains uniformly in the
resolvent for all sufficiently small perturbation parameters.  This is the compact-set form of
the resolvent-stability argument used to separate the noncritical spectrum in Proposition 2.1. -/
theorem eventually_forall_affinePencil_isInvertible_on_compact
    (B : Dom →L[ℂ] X) {K : Set ℂ} (hK : IsCompact K)
    (hres : ∀ z ∈ K, (S.affinePencil B 0 z).IsInvertible) :
    ∀ᶠ q in nhds 0, ∀ z ∈ K, (S.affinePencil B q z).IsInvertible := by
  let U : Set (Dom →L[ℂ] X) :=
    Set.range ((↑) : (Dom ≃L[ℂ] X) → Dom →L[ℂ] X)
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen
  apply hK.eventually_forall_of_forall_eventually
  intro z hz
  have hbase : S.affinePencil B 0 z ∈ U := hres z hz
  have hpreimage :
      (fun p : ℂ × ℂ ↦ S.affinePencil B p.1 p.2) ⁻¹' U ∈ nhds (0, z) :=
    (S.contDiff_affinePencil B).continuous.continuousAt (hU.mem_nhds hbase)
  filter_upwards [hpreimage] with p hp
  exact hp

/-- The Fredholm-complement block is holomorphic in `(q,z)`. -/
theorem contDiff_complementPencil (B : Dom →L[ℂ] X) :
    ContDiff ℂ ω (fun p : ℂ × ℂ ↦ S.complementPencil B p.1 p.2) := by
  unfold complementPencil affinePencil
  fun_prop

/-- The complementary block at `(0,0)` is invertible. -/
theorem complementPencil_zero_zero_isInvertible (B : Dom →L[ℂ] X) :
    (S.complementPencil B 0 0).IsInvertible := by
  refine ⟨S.complementOperatorEquiv, ?_⟩
  exact (S.complementPencil_zero_zero B).symm

/-- The inverse complementary block is holomorphic at `(0,0)`. -/
theorem contDiffAt_complementPencil_inverse (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω
      (fun p : ℂ × ℂ ↦ (S.complementPencil B p.1 p.2).inverse) (0, 0) := by
  have hinverse : ContDiffAt ℂ ω ContinuousLinearMap.inverse
      (S.complementPencil B 0 0) :=
    (S.complementPencil_zero_zero_isInvertible B).contDiffAt_map_inverse
  have hcomp := hinverse.comp (0, 0) (S.contDiff_complementPencil B).contDiffAt
  exact hcomp.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)

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

/-! ## The normalized kernel candidate for a general spectral parameter -/

/-- The Schur-complement correction of the neutral mode for the general pencil
`A₀-qB-z i`. -/
def kernelCorrection (B : Dom →L[ℂ] X) (q z : ℂ) : S.domainComplement :=
  -((S.complementPencil B q z).inverse
    (S.complementProjection (S.affinePencil B q z S.mode)))

/-- The corresponding normalized candidate for a kernel vector. -/
def kernelCandidate (B : Dom →L[ℂ] X) (q z : ℂ) : Dom :=
  S.mode + (S.kernelCorrection B q z : Dom)

/-- The scalar Schur complement of the general pencil. -/
def characteristicValue (B : Dom →L[ℂ] X) (q z : ℂ) : ℂ :=
  S.functional (S.affinePencil B q z (S.kernelCandidate B q z))

/-- The complementary solution operator for the general two-parameter pencil. -/
def pencilComplementSolution (B : Dom →L[ℂ] X) (q z : ℂ) :
    X →L[ℂ] S.domainComplement :=
  (S.complementPencil B q z).inverse.comp S.complementProjection

@[simp]
theorem kernelCorrection_zero_zero (B : Dom →L[ℂ] X) :
    S.kernelCorrection B 0 0 = 0 := by
  simp [kernelCorrection]

@[simp]
theorem kernelCandidate_zero_zero (B : Dom →L[ℂ] X) :
    S.kernelCandidate B 0 0 = S.mode := by
  simp [kernelCandidate]

@[simp]
theorem characteristicValue_zero_zero (B : Dom →L[ℂ] X) :
    S.characteristicValue B 0 0 = 0 := by
  simp [characteristicValue]

/-- The normalized kernel correction is holomorphic at `(0,0)`. -/
theorem contDiffAt_kernelCorrection (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω
      (fun p : ℂ × ℂ ↦ S.kernelCorrection B p.1 p.2) (0, 0) := by
  have hinverse := S.contDiffAt_complementPencil_inverse B
  have hpencil := (S.contDiff_affinePencil B).contDiffAt (x := ((0, 0) : ℂ × ℂ))
  unfold kernelCorrection
  fun_prop

/-- Coordinates of the normalized general-pencil kernel candidate in the implicit eigenpair
equation. -/
def kernelCandidateCoordinates (B : Dom →L[ℂ] X) (p : ℂ × ℂ) :
    ℂ × (ℂ × S.domainComplement) :=
  (p.1, (p.2, S.kernelCorrection B p.1 p.2))

@[simp]
theorem kernelCandidateCoordinates_zero (B : Dom →L[ℂ] X) :
    S.kernelCandidateCoordinates B (0, 0) = (0, (0, 0)) := by
  simp [kernelCandidateCoordinates]

/-- The candidate-coordinate map is holomorphic at the origin. -/
theorem contDiffAt_kernelCandidateCoordinates (B : Dom →L[ℂ] X) :
    ContDiffAt ℂ ω (S.kernelCandidateCoordinates B) (0, 0) := by
  have hcorrection := S.contDiffAt_kernelCorrection B
  unfold kernelCandidateCoordinates
  fun_prop

/-- The implicit eigenpair equation at the candidate coordinates is exactly the general pencil
applied to the normalized kernel candidate. -/
theorem eigenpairEquation_kernelCandidateCoordinates
    (B : Dom →L[ℂ] X) (q z : ℂ) :
    S.eigenpairEquation B (S.kernelCandidateCoordinates B (q, z)) =
      S.affinePencil B q z (S.kernelCandidate B q z) :=
  rfl

/-- The kernel candidate retains the fixed phase normalization exactly. -/
theorem kernelCandidate_normalized (B : Dom →L[ℂ] X) (q z : ℂ) :
    S.functional (S.inclusion (S.kernelCandidate B q z)) = 1 := by
  have hcorrection :
      S.functional (S.inclusion ((S.kernelCorrection B q z : S.domainComplement) : Dom)) = 0 :=
    (S.kernelCorrection B q z).property
  simp [kernelCandidate, S.normalized, hcorrection]

/-- In particular, the normalized kernel candidate never vanishes. -/
theorem kernelCandidate_ne_zero (B : Dom →L[ℂ] X) (q z : ℂ) :
    S.kernelCandidate B q z ≠ 0 := by
  intro hzero
  have hnormal := S.kernelCandidate_normalized B q z
  rw [hzero, map_zero, map_zero] at hnormal
  exact zero_ne_one hnormal

/-- If the complementary block is invertible, the correction cancels the complementary image
of the neutral mode. -/
theorem complementPencil_kernelCorrection
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible) :
    S.complementPencil B q z (S.kernelCorrection B q z) =
      -S.complementProjection (S.affinePencil B q z S.mode) := by
  simp only [kernelCorrection, map_neg]
  rw [hC.self_apply_inverse]

/-- The pencil image of the kernel candidate has no Fredholm-complement component. -/
theorem complementProjection_affinePencil_kernelCandidate
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible) :
    S.complementProjection (S.affinePencil B q z (S.kernelCandidate B q z)) = 0 := by
  rw [kernelCandidate, map_add, map_add]
  change S.complementProjection (S.affinePencil B q z S.mode) +
      S.complementPencil B q z (S.kernelCorrection B q z) = 0
  rw [S.complementPencil_kernelCorrection B q z hC, add_neg_cancel]

/-- A vector with vanishing complementary projection is its phase coefficient times the
embedded neutral mode. -/
theorem eq_functional_smul_inclusion_mode_of_complementProjection_eq_zero
    (w : X) (hw : S.complementProjection w = 0) :
    w = S.functional w • S.inclusion S.mode := by
  have hval := congrArg Subtype.val hw
  change w - S.projection w = 0 at hval
  rw [sub_eq_zero] at hval
  simpa only [S.projection_apply] using hval

/-- Schur-complement identity: the general pencil maps its normalized candidate to the scalar
characteristic value times the neutral mode. -/
theorem affinePencil_kernelCandidate
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible) :
    S.affinePencil B q z (S.kernelCandidate B q z) =
      S.characteristicValue B q z • S.inclusion S.mode := by
  exact S.eq_functional_smul_inclusion_mode_of_complementProjection_eq_zero _
    (S.complementProjection_affinePencil_kernelCandidate B q z hC)

/-- Vanishing of the scalar Schur complement produces a nonzero normalized kernel vector. -/
theorem kernelCandidate_mem_kernel_of_characteristicValue_eq_zero
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible)
    (hzero : S.characteristicValue B q z = 0) :
    S.affinePencil B q z (S.kernelCandidate B q z) = 0 := by
  rw [S.affinePencil_kernelCandidate B q z hC, hzero, zero_smul]

/-- The general complementary solution solves the projected pencil equation. -/
theorem complementPencil_pencilComplementSolution
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible) (w : X) :
    S.complementPencil B q z (S.pencilComplementSolution B q z w) =
      S.complementProjection w := by
  exact hC.self_apply_inverse (S.complementProjection w)

/-- Decomposition of an ambient vector into a neutral residual and a general-pencil value. -/
theorem eq_residual_add_affinePencil_pencilComplementSolution
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible) (w : X) :
    w =
      S.functional
          (w - S.affinePencil B q z
            ((S.pencilComplementSolution B q z w : S.domainComplement) : Dom)) •
        S.inclusion S.mode +
      S.affinePencil B q z
        ((S.pencilComplementSolution B q z w : S.domainComplement) : Dom) := by
  let u : S.domainComplement := S.pencilComplementSolution B q z w
  let r : X := w - S.affinePencil B q z (u : Dom)
  have hcomp : S.complementProjection r = 0 := by
    rw [show r = w - S.affinePencil B q z (u : Dom) by rfl, map_sub]
    change S.complementProjection w - S.complementPencil B q z u = 0
    rw [S.complementPencil_pencilComplementSolution B q z hC w, sub_self]
  have hr := S.eq_functional_smul_inclusion_mode_of_complementProjection_eq_zero r hcomp
  have hr' :
      w - S.affinePencil B q z (u : Dom) =
        S.functional (w - S.affinePencil B q z (u : Dom)) • S.inclusion S.mode := by
    simpa only [r] using hr
  exact (sub_eq_iff_eq_add).mp hr'

/-- Every kernel vector of the general pencil is a scalar multiple of the normalized kernel
candidate, provided the complementary block is invertible. -/
theorem eq_smul_kernelCandidate_of_affinePencil_eq_zero
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible)
    (x : Dom) (hxzero : S.affinePencil B q z x = 0) :
    x = S.functional (S.inclusion x) • S.kernelCandidate B q z := by
  let a : ℂ := S.functional (S.inclusion x)
  let x₀ : S.domainComplement := S.domainComplementPart x
  let k : S.domainComplement := S.kernelCorrection B q z
  have hx : x = a • S.mode + (x₀ : Dom) := by
    simpa [a, x₀] using S.domain_eq_neutral_add_complement x
  have hprojected :
      a • S.complementProjection (S.affinePencil B q z S.mode) +
        S.complementPencil B q z x₀ = 0 := by
    have h := congrArg S.complementProjection hxzero
    rw [map_zero] at h
    have h' :
        a • S.complementProjection (S.affinePencil B q z S.mode) +
          S.complementProjection (S.affinePencil B q z (x₀ : Dom)) = 0 := by
      simpa only [hx, map_add, map_smul] using h
    exact h'
  have hx₀ : x₀ = a • k := by
    apply hC.injective
    rw [map_smul]
    have hk := S.complementPencil_kernelCorrection B q z hC
    change S.complementPencil B q z x₀ = a • S.complementPencil B q z k
    rw [hk]
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_right hprojected
  change x = a • S.kernelCandidate B q z
  rw [hx, hx₀]
  simp only [kernelCandidate, k, Submodule.coe_smul, smul_add]

/-- A nonzero Schur complement makes the general pencil injective. -/
theorem affinePencil_injective_of_characteristicValue_ne_zero
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible)
    (hchar : S.characteristicValue B q z ≠ 0) :
    Injective (S.affinePencil B q z) := by
  intro x y hxy
  have hzero : S.affinePencil B q z (x - y) = 0 := by
    simpa only [map_sub, sub_eq_zero] using hxy
  have hrepr := S.eq_smul_kernelCandidate_of_affinePencil_eq_zero B q z hC (x - y) hzero
  have himage := congrArg (S.affinePencil B q z) hrepr
  rw [map_smul, S.affinePencil_kernelCandidate B q z hC, hzero] at himage
  have ha : S.functional (S.inclusion (x - y)) = 0 := by
    have hsmul :
        (S.functional (S.inclusion (x - y)) * S.characteristicValue B q z) •
          S.inclusion S.mode = 0 := by
      simpa only [smul_smul] using himage.symm
    have hprod :
        S.functional (S.inclusion (x - y)) * S.characteristicValue B q z = 0 :=
      (smul_eq_zero_iff_left S.inclusion_mode_ne_zero).mp hsmul
    exact (mul_eq_zero.mp hprod).resolve_right hchar
  apply sub_eq_zero.mp
  rw [hrepr, ha, zero_smul]

/-- A nonzero Schur complement makes the general pencil surjective. -/
theorem affinePencil_surjective_of_characteristicValue_ne_zero
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible)
    (hchar : S.characteristicValue B q z ≠ 0) :
    Surjective (S.affinePencil B q z) := by
  intro w
  let u : S.domainComplement := S.pencilComplementSolution B q z w
  let r : X := w - S.affinePencil B q z (u : Dom)
  let a : ℂ := S.functional r / S.characteristicValue B q z
  refine ⟨(u : Dom) + a • S.kernelCandidate B q z, ?_⟩
  rw [map_add, map_smul, S.affinePencil_kernelCandidate B q z hC]
  have hscalar :
      a • (S.characteristicValue B q z • S.inclusion S.mode) =
        S.functional r • S.inclusion S.mode := by
    rw [smul_smul]
    change (S.functional r / S.characteristicValue B q z *
      S.characteristicValue B q z) • S.inclusion S.mode = _
    rw [div_mul_cancel₀ _ hchar]
  rw [hscalar]
  have hr : r = S.functional r • S.inclusion S.mode := by
    have hdecomp :=
      S.eq_residual_add_affinePencil_pencilComplementSolution B q z hC w
    change w = S.functional r • S.inclusion S.mode +
      S.affinePencil B q z (u : Dom) at hdecomp
    dsimp only [r]
    calc
      w - S.affinePencil B q z (u : Dom) =
          (S.functional r • S.inclusion S.mode +
            S.affinePencil B q z (u : Dom)) -
              S.affinePencil B q z (u : Dom) := by rw [hdecomp]
      _ = S.functional r • S.inclusion S.mode := by abel
  rw [← hr]
  dsimp only [r]
  abel

/-- A nonzero Schur complement upgrades the general pencil to a Banach-space isomorphism. -/
theorem affinePencil_isInvertible_of_characteristicValue_ne_zero
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible)
    (hchar : S.characteristicValue B q z ≠ 0) :
    (S.affinePencil B q z).IsInvertible := by
  let e : Dom ≃L[ℂ] X := ContinuousLinearEquiv.ofBijective (S.affinePencil B q z)
    (LinearMap.ker_eq_bot.mpr
      (S.affinePencil_injective_of_characteristicValue_ne_zero B q z hC hchar))
    (LinearMap.range_eq_top.mpr
      (S.affinePencil_surjective_of_characteristicValue_ne_zero B q z hC hchar))
  exact ⟨e, rfl⟩

/-- With an invertible complementary block, failure of invertibility of the full pencil is
equivalent to vanishing of its scalar Schur complement. -/
theorem not_affinePencil_isInvertible_iff_characteristicValue_eq_zero
    (B : Dom →L[ℂ] X) (q z : ℂ)
    (hC : (S.complementPencil B q z).IsInvertible) :
    ¬(S.affinePencil B q z).IsInvertible ↔ S.characteristicValue B q z = 0 := by
  constructor
  · contrapose!
    exact S.affinePencil_isInvertible_of_characteristicValue_ne_zero B q z hC
  · intro hzero hinvertible
    have hkernel :=
      S.kernelCandidate_mem_kernel_of_characteristicValue_eq_zero B q z hC hzero
    have hcandzero : S.kernelCandidate B q z = 0 :=
      hinvertible.injective (by simpa only [map_zero] using hkernel)
    exact S.kernelCandidate_ne_zero B q z hcandzero

/-! ## Local uniqueness of the critical spectral point -/

/-- The implicit-function uniqueness neighborhood, pulled back along the normalized kernel
candidate.  Any nearby candidate that solves the eigenpair equation is the constructed branch. -/
theorem eventually_eigenpairBranch_eq_kernelCandidateCoordinates_of_eq_zero
    (B : Dom →L[ℂ] X) :
    ∀ᶠ p in nhds (0, 0),
      S.eigenpairEquation B (S.kernelCandidateCoordinates B p) = 0 →
        S.eigenpairBranch B p.1 =
          (p.2, S.kernelCorrection B p.1 p.2) := by
  have hIFT :
      ∀ᶠ v in nhds (0, (0, 0)),
        S.eigenpairEquation B v = 0 ↔ S.eigenpairBranch B v.1 = v.2 := by
    simpa only [S.eigenpairEquation_zero, eigenpairBranch] using
      (S.contDiff_eigenpairEquation B).contDiffAt.eventually_apply_eq_iff_implicitFunction
        (by simp) (S.eigenpairEquation_partialDerivative_isInvertible B)
  have hcoordinates :
      Tendsto (S.kernelCandidateCoordinates B) (nhds (0, 0))
        (nhds (0, (0, 0))) := by
    have h := (S.contDiffAt_kernelCandidateCoordinates B).continuousAt
    have h' : Tendsto (S.kernelCandidateCoordinates B) (nhds (0, 0))
        (nhds (S.kernelCandidateCoordinates B (0, 0))) := h
    simpa only [S.kernelCandidateCoordinates_zero B] using h'
  filter_upwards [hcoordinates.eventually hIFT] with p hp
  exact fun hzero ↦ hp.mp hzero

/-- In a neighborhood of `(q,z)=(0,0)`, failure of invertibility of the full pencil occurs
exactly on the Lyapunov--Schmidt eigenvalue graph `z=λ(q)`.  This supplies the local spectral
uniqueness part of analytic perturbation theory. -/
theorem eventually_not_affinePencil_isInvertible_iff_eq_eigenvalueBranch
    (B : Dom →L[ℂ] X) :
    ∀ᶠ p in nhds (0, 0),
      ¬(S.affinePencil B p.1 p.2).IsInvertible ↔
        p.2 = S.eigenvalueBranch B p.1 := by
  have heigenpair :
      ∀ᶠ p : ℂ × ℂ in nhds (0, 0),
        S.operator (S.eigenvectorBranch B p.1) -
            p.1 • B (S.eigenvectorBranch B p.1) =
          S.eigenvalueBranch B p.1 •
            S.inclusion (S.eigenvectorBranch B p.1) := by
    have hfst : Tendsto (fun p : ℂ × ℂ ↦ p.1) (nhds (0, 0)) (nhds 0) :=
      continuousAt_fst
    exact hfst.eventually (S.eventually_eigenvalue_equation B)
  filter_upwards [S.eventually_complementPencil_isInvertible B,
    S.eventually_eigenpairBranch_eq_kernelCandidateCoordinates_of_eq_zero B,
    heigenpair] with p hC hunique heigen
  constructor
  · intro hnot
    have hchar : S.characteristicValue B p.1 p.2 = 0 :=
      (S.not_affinePencil_isInvertible_iff_characteristicValue_eq_zero
        B p.1 p.2 hC).mp hnot
    have hkernel :=
      S.kernelCandidate_mem_kernel_of_characteristicValue_eq_zero B p.1 p.2 hC hchar
    have hequation :
        S.eigenpairEquation B (S.kernelCandidateCoordinates B p) = 0 := by
      rw [S.eigenpairEquation_kernelCandidateCoordinates]
      exact hkernel
    have hbranch := hunique hequation
    have hfirst := congrArg Prod.fst hbranch
    simpa only [eigenvalueBranch] using hfirst.symm
  · intro hz hinvertible
    have hkernel :
        S.affinePencil B p.1 p.2 (S.eigenvectorBranch B p.1) = 0 := by
      rw [hz]
      simpa only [affinePencil_apply, sub_eq_zero] using heigen
    have hvector_ne : S.eigenvectorBranch B p.1 ≠ 0 := by
      intro hzero
      have hnormal := S.eigenvectorBranch_normalized B p.1
      rw [hzero, map_zero, map_zero] at hnormal
      exact zero_ne_one hnormal
    apply hvector_ne
    apply hinvertible.injective
    simpa only [map_zero] using hkernel

/-- For maps between the Banach graph domain and ambient space, Mathlib's bundled notion of
invertibility is equivalent to algebraic bijectivity. -/
theorem affinePencil_isInvertible_iff_bijective
    (B : Dom →L[ℂ] X) (q z : ℂ) :
    (S.affinePencil B q z).IsInvertible ↔
      Function.Bijective (S.affinePencil B q z) := by
  constructor
  · exact ContinuousLinearMap.IsInvertible.bijective
  · intro hbij
    refine ⟨ContinuousLinearEquiv.ofBijective (S.affinePencil B q z)
      (LinearMap.ker_eq_bot.mpr hbij.injective)
      (LinearMap.range_eq_top.mpr hbij.surjective), rfl⟩

/-- Bijectivity form of the local spectral-graph theorem. -/
theorem eventually_not_bijective_affinePencil_iff_eq_eigenvalueBranch
    (B : Dom →L[ℂ] X) :
    ∀ᶠ p in nhds (0, 0),
      ¬Function.Bijective (S.affinePencil B p.1 p.2) ↔
        p.2 = S.eigenvalueBranch B p.1 := by
  filter_upwards [S.eventually_not_affinePencil_isInvertible_iff_eq_eigenvalueBranch B]
    with p hp
  rw [← hp, S.affinePencil_isInvertible_iff_bijective B p.1 p.2]

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

/-- Pointwise form of the perturbed Fredholm alternative at the critical eigenvalue. -/
theorem range_criticalPencil_eq_kernel_criticalCokernelFunctional
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible)
    (heig : S.criticalPencil B q (S.eigenvectorBranch B q) = 0) :
    LinearMap.range (S.criticalPencil B q).toLinearMap =
      LinearMap.ker (S.criticalCokernelFunctional B q).toLinearMap := by
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

/-- The embedded critical eigenvector is nonzero for every parameter, as its original phase
normalization is exactly one. -/
theorem inclusion_eigenvectorBranch_ne_zero (B : Dom →L[ℂ] X) (q : ℂ) :
    S.inclusion (S.eigenvectorBranch B q) ≠ 0 := by
  intro hzero
  have hnormal := S.eigenvectorBranch_normalized B q
  rw [hzero, map_zero] at hnormal
  exact zero_ne_one hnormal

/-- The normalized perturbed left functional is nonzero whenever its normalization denominator
is nonzero. -/
theorem criticalLeftFunctional_ne_zero
    (B : Dom →L[ℂ] X) (q : ℂ) (hq : S.criticalNormalization B q ≠ 0) :
    S.criticalLeftFunctional B q ≠ 0 := by
  intro hzero
  have hnormal := S.criticalLeftFunctional_eigenvector B q hq
  rw [hzero, zero_apply] at hnormal
  exact zero_ne_one hnormal

/-- The range of the critical projection is exactly the perturbed critical eigenline. -/
theorem range_criticalProjection_eq_span
    (B : Dom →L[ℂ] X) (q : ℂ) (hq : S.criticalNormalization B q ≠ 0) :
    LinearMap.range (S.criticalProjection B q).toLinearMap =
      Submodule.span ℂ {S.inclusion (S.eigenvectorBranch B q)} := by
  simpa [criticalProjection] using
    ContinuousLinearMap.range_smulRight_apply
      (S.criticalLeftFunctional_ne_zero B q hq)
      (S.inclusion (S.eigenvectorBranch B q))

/-- The critical projection has rank one whenever its normalization denominator is nonzero. -/
theorem finrank_range_criticalProjection
    (B : Dom →L[ℂ] X) (q : ℂ) (hq : S.criticalNormalization B q ≠ 0) :
    Module.finrank ℂ (LinearMap.range (S.criticalProjection B q).toLinearMap) = 1 := by
  rw [S.range_criticalProjection_eq_span B q hq]
  exact finrank_span_singleton (S.inclusion_eigenvectorBranch_ne_zero B q)

/-- The projection kernel is the kernel of the normalized perturbed left functional. -/
theorem kernel_criticalProjection_eq_kernel_criticalLeftFunctional
    (B : Dom →L[ℂ] X) (q : ℂ) :
    LinearMap.ker (S.criticalProjection B q).toLinearMap =
      LinearMap.ker (S.criticalLeftFunctional B q).toLinearMap := by
  ext w
  simp only [LinearMap.mem_ker]
  exact smul_eq_zero_iff_left (S.inclusion_eigenvectorBranch_ne_zero B q)

/-- Normalizing by a nonzero scalar does not change the cokernel hyperplane. -/
theorem kernel_criticalLeftFunctional_eq_kernel_criticalCokernelFunctional
    (B : Dom →L[ℂ] X) (q : ℂ) (hq : S.criticalNormalization B q ≠ 0) :
    LinearMap.ker (S.criticalLeftFunctional B q).toLinearMap =
      LinearMap.ker (S.criticalCokernelFunctional B q).toLinearMap := by
  ext w
  simp only [LinearMap.mem_ker]
  change (S.criticalNormalization B q)⁻¹ *
      S.criticalCokernelFunctional B q w = 0 ↔
    S.criticalCokernelFunctional B q w = 0
  simp [hq]

/-- The spectral splitting identity: the critical projection kernel is precisely the range of
the shifted operator at the critical eigenvalue. -/
theorem kernel_criticalProjection_eq_range_criticalPencil
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible)
    (heig : S.criticalPencil B q (S.eigenvectorBranch B q) = 0)
    (hq : S.criticalNormalization B q ≠ 0) :
    LinearMap.ker (S.criticalProjection B q).toLinearMap =
      LinearMap.range (S.criticalPencil B q).toLinearMap := by
  rw [S.kernel_criticalProjection_eq_kernel_criticalLeftFunctional B q,
    S.kernel_criticalLeftFunctional_eq_kernel_criticalCokernelFunctional B q hq,
    ← S.range_criticalPencil_eq_kernel_criticalCokernelFunctional B q hC heig]

/-- Near zero, the projection has rank one and its kernel is exactly the range of the shifted
critical pencil. -/
theorem eventually_criticalProjection_spectralSplitting (B : Dom →L[ℂ] X) :
    ∀ᶠ q in nhds 0,
      Module.finrank ℂ (LinearMap.range (S.criticalProjection B q).toLinearMap) = 1 ∧
      LinearMap.ker (S.criticalProjection B q).toLinearMap =
        LinearMap.range (S.criticalPencil B q).toLinearMap := by
  filter_upwards [S.eventually_criticalComplementPencil_isInvertible B,
    S.eventually_criticalPencil_eigenvector_eq_zero B,
    S.eventually_criticalNormalization_ne_zero B] with q hC heig hq
  exact ⟨S.finrank_range_criticalProjection B q hq,
    S.kernel_criticalProjection_eq_range_criticalPencil B q hC heig hq⟩

/-- The actual perturbed projection has the operator-norm estimate `P(q)-P(0)=O(q)`. -/
theorem criticalProjection_sub_projection_isBigO (B : Dom →L[ℂ] X) :
    (fun q ↦ S.criticalProjection B q - S.projection) =O[nhds 0]
      fun q : ℂ ↦ q := by
  have h := ((S.contDiffAt_criticalProjection B).differentiableAt (by simp)).hasFDerivAt.isBigO_sub
  simpa only [S.criticalProjection_zero, sub_zero] using h

end SimpleFredholmZeroMode
end Planarwave
