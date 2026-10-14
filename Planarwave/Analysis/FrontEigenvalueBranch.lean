/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

import all Planarwave.Analysis.FrontCoefficient
import all Planarwave.Analysis.SimpleSpectralProjection

/-!
# The critical transverse eigenvalue branch

This file specializes the Lyapunov--Schmidt construction to the planar front.  It formalizes the
local analytic part of Proposition 2.1 in the cited paper: for the analytic parameter `q = k²`,
the simple eigenvalue issuing from the translational eigenvalue satisfies

`λ(q) = -d_perp q + O(q²)`,

and hence `λ(k²) = -d_perp k² + O(k⁴)` for real transverse wavenumber `k`.  The file also proves
that this branch is the only nearby spectrum and constructs its holomorphic rank-one spectral
projection, with `P(k²) = P(0) + O(k²)`.
-/

open Filter Function
open Asymptotics
open scoped Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ ψ : ℝ → ℝ^n)
  (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ)

/-- The critical eigenvalue as a function of the analytic parameter `q = k²`. -/
def frontCriticalEigenvalue (q : ℂ) : ℂ :=
  (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvalueBranch
    (diffusionValue (frontComplexifiedDiffusion D)) q

/-- The corresponding adjoint-normalized eigenvector in the common graph domain. -/
def frontCriticalEigenvector (q : ℂ) : ComplexBUC2 (ℂ^n) :=
  (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvectorBranch
    (diffusionValue (frontComplexifiedDiffusion D)) q

@[simp]
theorem frontCriticalEigenvalue_zero :
    frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ 0 = 0 := by
  simp [frontCriticalEigenvalue]

/-- The critical eigenvalue depends holomorphically on the analytic parameter at zero. -/
theorem contDiffAt_frontCriticalEigenvalue :
    ContDiffAt ℂ ⊤ (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃) 0 := by
  exact (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).contDiffAt_eigenvalueBranch
    (diffusionValue (frontComplexifiedDiffusion D))

@[simp]
theorem frontCriticalEigenvector_zero :
    frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ 0 =
      translationModeComplexBUC2 f D c φ ψ h₃ := by
  simp [frontCriticalEigenvector, frontHorizontalSimpleFredholmZeroMode,
    horizontalSimpleFredholmZeroMode]

/-! ## Local critical spectrum and its spectral projection -/

/-- The concrete common-domain pencil `L(q) - z` is exactly the abstract affine pencil used in
the Lyapunov--Schmidt reduction. -/
theorem frontLongitudinalResolvent_eq_affinePencil (q z : ℂ) :
    frontLongitudinalPencil f D c φ h₁ h₂ q -
        z • ComplexBUC2.valueCLM (ℂ^n) =
      (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).affinePencil
        (diffusionValue (frontComplexifiedDiffusion D)) q z := by
  rw [frontLongitudinalPencil_eq_zero_sub, frontLongitudinalPencil_zero]
  rfl

/-- At a real transverse wavenumber, the challenge resolvent is the same affine pencil with
analytic parameter `q = k²`. -/
theorem frontChallengeResolventMap_eq_affinePencil (k : ℝ) (z : ℂ) :
    frontChallengeResolventMap f D c φ h₁ h₂ k z =
      (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).affinePencil
        (diffusionValue (frontComplexifiedDiffusion D)) (k ^ 2) z := by
  rw [← frontLongitudinalResolvent_eq_affinePencil f D c φ ψ h₁ h₂ h₃ (k ^ 2) z]
  rfl

/-- In the analytic parameter `(q,z)`, the only nearby failure of bijectivity is the critical
eigenvalue branch. -/
theorem eventually_frontLongitudinalPencil_not_bijective_iff :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0),
      ¬ Function.Bijective
          (frontLongitudinalPencil f D c φ h₁ h₂ p.1 -
            p.2 • ComplexBUC2.valueCLM (ℂ^n)) ↔
        p.2 = frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ p.1 := by
  let S := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let B := diffusionValue (frontComplexifiedDiffusion D)
  filter_upwards [S.eventually_not_bijective_affinePencil_iff_eq_eigenvalueBranch B]
    with p hp
  rw [frontLongitudinalResolvent_eq_affinePencil f D c φ ψ h₁ h₂ h₃]
  simpa [frontCriticalEigenvalue, S, B] using hp

include ψ h₃

/-- Every compact set of horizontal resolvent points remains in the resolvent of the analytic
front pencil for all sufficiently small `q`. -/
theorem eventually_frontLongitudinalPencil_bijective_on_compact_horizontal_resolvent
    {K : Set ℂ} (hK : IsCompact K)
    (hres : ∀ z ∈ K, z ∉ TransverseSpectrum f D c φ 0) :
    ∀ᶠ q in 𝓝 0, ∀ z ∈ K,
      Function.Bijective
        (frontLongitudinalPencil f D c φ h₁ h₂ q -
          z • ComplexBUC2.valueCLM (ℂ^n)) := by
  let S := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let B := diffusionValue (frontComplexifiedDiffusion D)
  have hres' : ∀ z ∈ K, (S.affinePencil B 0 z).IsInvertible := by
    intro z hz
    apply (S.affinePencil_isInvertible_iff_bijective B 0 z).2
    have hbij :
        Function.Bijective (frontChallengeResolventMap f D c φ h₁ h₂ 0 z) := by
      by_contra hnot
      exact hres z hz
        ((mem_transverseSpectrum_iff_frontChallengeResolventMap_not_bijective
          f D c φ h₁ h₂ 0 z).2 hnot)
    rw [frontChallengeResolventMap_eq_affinePencil f D c φ ψ h₁ h₂ h₃] at hbij
    simpa [S, B] using hbij
  filter_upwards [S.eventually_forall_affinePencil_isInvertible_on_compact B hK hres']
    with q hq
  intro z hz
  rw [frontLongitudinalResolvent_eq_affinePencil f D c φ ψ h₁ h₂ h₃]
  exact (S.affinePencil_isInvertible_iff_bijective B q z).1 (hq z hz)

/-- Compact-window version of Proposition 2.1(1).  The horizontal spectral gap excludes every
nonzero point of a compact subset of `Re z ≥ -θ/2`, and compact resolvent stability preserves
that exclusion for all sufficiently small complex perturbation parameters. -/
theorem exists_eventually_frontLongitudinalPencil_bijective_on_compact_gap :
    ∃ θ > 0, ∀ K : Set ℂ, IsCompact K →
      (∀ z ∈ K, z ≠ 0 ∧ -(θ / 2) ≤ z.re) →
      ∀ᶠ q in 𝓝 0, ∀ z ∈ K,
        Function.Bijective
          (frontLongitudinalPencil f D c φ h₁ h₂ q -
            z • ComplexBUC2.valueCLM (ℂ^n)) := by
  obtain ⟨θ, hθ, hgap⟩ := h₃.horizontal_spectral_gap
  refine ⟨θ, hθ, ?_⟩
  intro K hK hregion
  apply eventually_frontLongitudinalPencil_bijective_on_compact_horizontal_resolvent
    f D c φ ψ h₁ h₂ h₃ hK
  intro z hz hspec
  rcases hgap z hspec with hzero | hleft
  · exact (hregion z hz).1 hzero
  · have hright := (hregion z hz).2
    linarith

/-- Explicit bounded-window form of compact spectral separation.  For every inner radius `r>0`
and outer radius `R`, the part of `Re z ≥ -θ/2` with `r ≤ ‖z‖ ≤ R` is uniformly in the
resolvent for all sufficiently small complex `q`. -/
theorem exists_eventually_frontLongitudinalPencil_bijective_on_bounded_gap :
    ∃ θ > 0, ∀ r > 0, ∀ R : ℝ,
      ∀ᶠ q in 𝓝 0, ∀ z : ℂ,
        r ≤ ‖z‖ → ‖z‖ ≤ R → -(θ / 2) ≤ z.re →
          Function.Bijective
            (frontLongitudinalPencil f D c φ h₁ h₂ q -
              z • ComplexBUC2.valueCLM (ℂ^n)) := by
  obtain ⟨θ, hθ, hcompact⟩ :=
    exists_eventually_frontLongitudinalPencil_bijective_on_compact_gap
      f D c φ ψ h₁ h₂ h₃
  refine ⟨θ, hθ, ?_⟩
  intro r hr R
  let K : Set ℂ :=
    (Metric.closedBall 0 R ∩ {z : ℂ | r ≤ ‖z‖}) ∩
      {z : ℂ | -(θ / 2) ≤ z.re}
  have hK : IsCompact K := by
    apply ((isCompact_closedBall (0 : ℂ) R).inter_right
      (isClosed_le continuous_const continuous_norm)).inter_right
    exact isClosed_le continuous_const Complex.continuous_re
  have hregion : ∀ z ∈ K, z ≠ 0 ∧ -(θ / 2) ≤ z.re := by
    intro z hz
    refine ⟨?_, hz.2⟩
    intro hzero
    subst z
    have hr0 : r ≤ 0 := by simpa using hz.1.2
    linarith
  filter_upwards [hcompact K hK hregion] with q hq
  intro z hrz hRz hRez
  apply hq z
  change (z ∈ Metric.closedBall (0 : ℂ) R ∧ r ≤ ‖z‖) ∧ -(θ / 2) ≤ z.re
  exact ⟨⟨by simpa [Metric.mem_closedBall] using hRz, hrz⟩, hRez⟩

/-- Bounded-window version of the full low-frequency spectral separation.  In any fixed disk,
the only possible spectrum in `Re z ≥ -θ/2` is the Lyapunov--Schmidt eigenvalue branch.  The
proof follows the paper's argument: use local analytic perturbation near zero and compact
resolvent stability on the surrounding annulus. -/
theorem exists_eventually_frontLongitudinalPencil_not_bijective_iff_branch_on_bounded_gap :
    ∃ θ > 0, ∀ R : ℝ,
      ∀ᶠ q in 𝓝 0, ∀ z : ℂ,
        ‖z‖ ≤ R → -(θ / 2) ≤ z.re →
          (¬ Function.Bijective
              (frontLongitudinalPencil f D c φ h₁ h₂ q -
                z • ComplexBUC2.valueCLM (ℂ^n)) ↔
            z = frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q) := by
  obtain ⟨θ, hθ, hgap⟩ :=
    exists_eventually_frontLongitudinalPencil_bijective_on_bounded_gap
      f D c φ ψ h₁ h₂ h₃
  have hlocal :=
    eventually_frontLongitudinalPencil_not_bijective_iff f D c φ ψ h₁ h₂ h₃
  rw [nhds_prod_eq] at hlocal
  obtain ⟨pq, hpq, pz, hpz, hrectangle⟩ := eventually_prod_iff.mp hlocal
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp hpz
  let S := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let B := diffusionValue (frontComplexifiedDiffusion D)
  have hbranchContinuous :
      ContinuousAt (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃) 0 := by
    change ContinuousAt (S.eigenvalueBranch B) 0
    exact (S.hasDerivAt_eigenvalueBranch B).continuousAt
  have hbranch :
      Tendsto (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃) (𝓝 0) (𝓝 0) := by
    change Tendsto (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃) (𝓝 0)
      (𝓝 (frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ 0)) at hbranchContinuous
    rw [frontCriticalEigenvalue_zero] at hbranchContinuous
    exact hbranchContinuous
  have hbranchBall :
      ∀ᶠ q in 𝓝 0,
        frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q ∈ Metric.ball 0 r :=
    hbranch (Metric.ball_mem_nhds 0 hr)
  refine ⟨θ, hθ, ?_⟩
  intro R
  filter_upwards [hpq, hbranchBall, hgap r hr R] with q hq hlambda hqgap
  intro z hRz hRez
  by_cases hz : ‖z‖ < r
  · apply hrectangle hq
    apply hrball
    simpa [Metric.mem_ball] using hz
  · constructor
    · intro hnot
      exact (hnot (hqgap z (le_of_not_gt hz) hRz hRez)).elim
    · intro hzeq
      exfalso
      apply hz
      rw [hzeq]
      simpa [Metric.mem_ball] using hlambda

/-- The shifted concrete pencil along the critical eigenvalue branch. -/
def frontCriticalShiftedPencil (q : ℂ) :
    ComplexBUC2 (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  frontLongitudinalPencil f D c φ h₁ h₂ q -
    frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q •
      ComplexBUC2.valueCLM (ℂ^n)

/-- The concrete shifted pencil is the abstract critical pencil. -/
theorem frontCriticalShiftedPencil_eq_criticalPencil (q : ℂ) :
    frontCriticalShiftedPencil f D c φ ψ h₁ h₂ h₃ q =
      (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).criticalPencil
        (diffusionValue (frontComplexifiedDiffusion D)) q := by
  rw [frontCriticalShiftedPencil,
    frontLongitudinalResolvent_eq_affinePencil f D c φ ψ h₁ h₂ h₃]
  rfl

/-- The rank-one spectral projection associated with the locally simple critical eigenvalue.
Its kernel is shown below to be the range of `L(q)-λ_c(q)`. -/
def frontCriticalProjection (q : ℂ) :
    BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n) :=
  (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).criticalProjection
    (diffusionValue (frontComplexifiedDiffusion D)) q

@[simp]
theorem frontCriticalProjection_zero :
    frontCriticalProjection f D c φ ψ h₁ h₂ h₃ 0 =
      profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) := by
  rw [frontCriticalProjection,
    (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).criticalProjection_zero]
  rfl

/-- The critical spectral projection depends holomorphically on `q` at zero. -/
theorem contDiffAt_frontCriticalProjection :
    ContDiffAt ℂ ⊤ (frontCriticalProjection f D c φ ψ h₁ h₂ h₃) 0 := by
  exact (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).contDiffAt_criticalProjection
    (diffusionValue (frontComplexifiedDiffusion D))

/-- Near zero, the critical spectral projection is idempotent. -/
theorem eventually_frontCriticalProjection_idempotent :
    ∀ᶠ q in 𝓝 0, ∀ w : BUC ℝ (ℂ^n),
      frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q
          (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q w) =
        frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q w := by
  let S := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let B := diffusionValue (frontComplexifiedDiffusion D)
  filter_upwards [S.eventually_criticalNormalization_ne_zero B] with q hq
  intro w
  have hnorm := S.criticalLeftFunctional_eigenvector B q hq
  dsimp only [S, B] at hnorm
  simp only [frontCriticalProjection, SimpleFredholmZeroMode.criticalProjection_apply,
    map_smul, hnorm, one_smul]

/-- The projection has rank one and its kernel is precisely the range of the shifted front
operator, which is the algebraic spectral splitting at the simple eigenvalue. -/
theorem eventually_frontCriticalProjection_spectralSplitting :
    ∀ᶠ q in 𝓝 0,
      Module.finrank ℂ
          (LinearMap.range
            (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q).toLinearMap) = 1 ∧
        LinearMap.ker
            (frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q).toLinearMap =
          LinearMap.range
            (frontCriticalShiftedPencil f D c φ ψ h₁ h₂ h₃ q).toLinearMap := by
  filter_upwards [
    (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eventually_criticalProjection_spectralSplitting
        (diffusionValue (frontComplexifiedDiffusion D))] with q hq
  rw [frontCriticalShiftedPencil_eq_criticalPencil f D c φ ψ h₁ h₂ h₃]
  exact hq

/-- In the analytic parameter, the critical spectral projection satisfies `P(q)-P(0)=O(q)`. -/
theorem frontCriticalProjection_sub_isBigO :
    (fun q ↦ frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q -
        profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃))
      =O[𝓝 0] fun q : ℂ ↦ q := by
  let S := frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃
  let B := diffusionValue (frontComplexifiedDiffusion D)
  have hP : S.projection =
      profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃) := by
    ext w
    rfl
  change (fun q ↦ S.criticalProjection B q -
    profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃))
      =O[𝓝 0] fun q : ℂ ↦ q
  rw [← hP]
  exact S.criticalProjection_sub_projection_isBigO B

/-- Near `q = 0`, the branch solves the concrete common-domain eigenvalue equation. -/
theorem eventually_frontCriticalEigenvalue_equation :
    ∀ᶠ q in 𝓝 0,
      frontLongitudinalPencil f D c φ h₁ h₂ q
          (frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ q) =
        frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q •
          ComplexBUC2.valueCLM (ℂ^n)
            (frontCriticalEigenvector f D c φ ψ h₁ h₂ h₃ q) := by
  filter_upwards [
    (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eventually_eigenvalue_equation
      (diffusionValue (frontComplexifiedDiffusion D))] with q hq
  rw [frontLongitudinalPencil_eq_zero_sub]
  rw [frontLongitudinalPencil_zero]
  simpa [frontCriticalEigenvalue, frontCriticalEigenvector,
    frontHorizontalSimpleFredholmZeroMode, horizontalSimpleFredholmZeroMode] using hq

/-- Proposition 2.1 in its natural analytic parameter: `λ(q) = -d_perp q + O(q²)`. -/
theorem frontCriticalEigenvalue_firstOrder_isBigO :
    (fun q => frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q +
        q * (d_perp D φ ψ : ℂ)) =O[𝓝 0] fun q : ℂ => q ^ 2 := by
  simpa only [frontCriticalEigenvalue,
    frontHorizontalSimpleFredholmZeroMode, horizontalSimpleFredholmZeroMode,
    phaseFunctional_diffusionValue_translationMode] using
    (frontHorizontalSimpleFredholmZeroMode f D c φ ψ h₁ h₂ h₃).eigenvalueBranch_firstOrder_isBigO
      (diffusionValue (frontComplexifiedDiffusion D))

/-- Positivity of the transverse diffusion coefficient, the first assertion in
Proposition 2.1(3). -/
theorem frontTransverseDiffusion_pos :
    0 < d_perp D φ ψ :=
  h₃.transverse_low_wavenumber

/-- One positive constant simultaneously controls the eigenvalue and spectral-projection Taylor
remainders in the analytic parameter, as in Proposition 2.1(3). -/
theorem exists_frontCriticalExpansion_bound :
    ∃ C₀ > 0, ∀ᶠ q in 𝓝 0,
      ‖frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q +
          q * (d_perp D φ ψ : ℂ)‖ ≤ C₀ * ‖q‖ ^ 2 ∧
        ‖frontCriticalProjection f D c φ ψ h₁ h₂ h₃ q -
          profileProjection ψ h₃.integrable (translationModeBUC f D c φ ψ h₃)‖ ≤
            C₀ * ‖q‖ := by
  obtain ⟨Ceig, hCeig, heig⟩ :=
    (frontCriticalEigenvalue_firstOrder_isBigO f D c φ ψ h₁ h₂ h₃).exists_pos
  obtain ⟨CP, hCP, hP⟩ :=
    (frontCriticalProjection_sub_isBigO f D c φ ψ h₁ h₂ h₃).exists_pos
  refine ⟨max Ceig CP, hCeig.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [heig.bound, hP.bound] with q heigq hPq
  constructor
  · calc
      ‖frontCriticalEigenvalue f D c φ ψ h₁ h₂ h₃ q +
          q * (d_perp D φ ψ : ℂ)‖ ≤ Ceig * ‖q ^ 2‖ := heigq
      _ = Ceig * ‖q‖ ^ 2 := by rw [norm_pow]
      _ ≤ max Ceig CP * ‖q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ‖q‖)
  · exact hPq.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg q))

end

end Planarwave
