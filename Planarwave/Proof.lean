/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Statement
import all Planarwave.Analysis.FrontTrackingGlobal
import all Planarwave.Analysis.FrontTrackingVHJComparison

/-!
# Imported proof of the planar-front challenge

The analytic proof uses the namespaced predicates from `Planarwave.Statement`.
The final transfer theorem accepts equivalent resolvent predicates and maps the
two solution records, allowing `Solution.lean` to copy the challenge verbatim
apart from this import and the replacement for its `sorry`.
-/

public section

open scoped Gradient Laplacian EuclideanGeometry Topology InnerProductSpace ContDiff
open Filter Function Set MeasureTheory

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {d n : ℕ} (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n)
  (c : ℝ) (φ ψ : ℝ → ℝ^n)

/-- The complete challenge statement, proved without importing the reference theorem. -/
theorem vHJ_approximates_planar_front_proved
  (hn : 1 ≤ n) (hd : 2 ≤ d)
  (h₁ : IsSmoothParabolic f D)
  (h₂ : IsSmoothFront f D c φ)
  (h₃ : IsSpectrallyStableWithAdjoint f D c φ ψ) :
  ∃ C > 0, ∃ ε > 0, ∀ E_0 ∈ Icc 0 ε, ∀ u₀ : ℝ^d → ℝ^n, IsBUC u₀ → IsCloseToFront φ u₀ E_0 →
    ∃ u σ, IsRDESolution f D u ∧ IsVHJSolution c σ (d_perp D φ ψ) ∧
      u 0 = u₀ ∧ (∀ y, σ 0 y = ∫ z, ⟪ψ z, φ z - u 0 (full y z)⟫_ℝ) ∧
      ∀ t ≥ 0, ∀ x, ‖u t x - φ (horizontal x - c * t - σ t (transverse x))‖ ≤
        C * E_0 * (E_0 + (1 + t)⁻¹ * Real.log (2 + t)) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : Nontrivial (ℝ^n) := inferInstance
  obtain ⟨_, _, εg, hεg, hglobal⟩ :=
    exists_front_global_solution_with_tracking f D c φ ψ h₁ h₂ h₃ hd
  obtain ⟨C, hC, εv, hεv, hcompare⟩ :=
    exists_front_tracking_vHJ_error_bound f D c φ ψ h₁ h₂ h₃ hd
  refine ⟨C, hC, min εg εv, lt_min hεg hεv, ?_⟩
  intro M hM u₀ hu₀ hclose
  let u₀b := BUC.ofIsBUC hu₀
  let v₀ := frontInverseModulatedPerturbation f D c φ h₂ hd u₀b 0 0
  have hcloseb : IsCloseToFront φ (u₀b : ℝ^d → ℝ^n) M := hclose
  have hv₀ : ‖v₀‖ ≤ M :=
    (norm_frontInverseModulatedPerturbation_zero_le_iff f D c φ h₂ hd u₀b hM.1).mpr hcloseb
  obtain ⟨u, hinit, hu, _, htracking⟩ :=
    hglobal u₀b v₀ M hM.1 (hM.2.trans (min_le_left _ _)) hv₀
      (by simp only [mul_zero]; rfl)
  refine ⟨(fun t x ↦ u t x),
    challengePhaseEvolution f D c φ ψ hd h₂ h₃ (isBUC_coe u₀b), hu,
    isVHJSolution_challengePhaseEvolution f D c φ ψ hd h₂ h₃ (isBUC_coe u₀b), ?_, ?_, ?_⟩
  · funext x
    change u 0 x = u₀ x
    rw [hinit]
    rfl
  · intro y
    simpa only [hinit] using
      challengePhaseEvolution_zero f D c φ ψ hd h₂ h₃ (isBUC_coe u₀b) y
  · intro t ht x
    obtain ⟨X, hXu, _, _⟩ := htracking t ht
    have hXinit : X.u 0 = u₀b := by rw [hXu, hinit]
    simpa only [hXu] using hcompare X u₀b hXinit
      ⟨hM.1, hM.2.trans (min_le_right _ _)⟩ hcloseb t ⟨ht, le_rfl⟩ x

/-- Transfer the proved theorem to independently declared challenge predicates.
Only the resolvent equivalence and the two solution-record conversions are
needed: all other copied definitions have the same bodies. -/
theorem vHJ_approximates_planar_front_of_equivalent_predicates
    (hn : 1 ≤ n) (hd : 2 ≤ d)
    {P : ℝ → ℂ → (ℝ → ℂ^n) → (ℝ → ℂ^n) → Prop}
    {R : (ℝ → ℝ^d → ℝ^n) → Prop}
    {V : (ℝ → ℝ^(d - 1) → ℝ) → Prop}
    (hP : ∀ k l v w, P k l v w ↔ IsTransverseResolventSolution f D c φ k l v w)
    (hR : ∀ u, IsRDESolution f D u → R u)
    (hV : ∀ σ, IsVHJSolution c σ (d_perp D φ ψ) → V σ)
    (h₁ : IsSmoothParabolic f D)
    (h₂ : IsSmoothFront f D c φ)
    (hintegrable : Integrable ψ)
    (hnormalized : ∫ x, ⟪ψ x, deriv φ x⟫_ℝ = 1)
    (hgap : ∃ θ > 0, ∀ l ∈ compl {l | ∀ w, IsBUC w → ∃! v, P 0 l v w},
      l = 0 ∨ l.re ≤ -θ)
    (hkernel : ∀ v, P 0 0 v 0 ↔ ∃ a : ℂ, ∀ x, v x = a • embed (deriv φ x))
    (hsolvability : ∀ w, IsBUC w →
      (∫ z, ⟪embed (ψ z), w z⟫_ℂ = 0 ↔ ∃ v, P 0 0 v w))
    (hlow : d_perp D φ ψ > 0)
    (hhigh : ∀ k₀ > 0, ∃ θ₁ > 0, ∀ k ≥ k₀,
      ∀ l ∈ compl {l | ∀ w, IsBUC w → ∃! v, P k l v w}, l.re ≤ -θ₁) :
    ∃ C > 0, ∃ ε > 0, ∀ E_0 ∈ Icc 0 ε, ∀ u₀ : ℝ^d → ℝ^n,
      IsBUC u₀ → IsCloseToFront φ u₀ E_0 →
      ∃ u σ, R u ∧ V σ ∧
        u 0 = u₀ ∧ (∀ y, σ 0 y = ∫ z, ⟪ψ z, φ z - u 0 (full y z)⟫_ℝ) ∧
        ∀ t ≥ 0, ∀ x, ‖u t x - φ (horizontal x - c * t - σ t (transverse x))‖ ≤
          C * E_0 * (E_0 + (1 + t)⁻¹ * Real.log (2 + t)) := by
  have hP_eq : P = IsTransverseResolventSolution f D c φ := by
    funext k l v w
    exact propext (hP k l v w)
  subst P
  obtain ⟨C, hC, ε, hε, hmain⟩ :=
    vHJ_approximates_planar_front_proved f D c φ ψ hn hd h₁ h₂
      ⟨hintegrable, hnormalized, hgap, hkernel, hsolvability, hlow, hhigh⟩
  refine ⟨C, hC, ε, hε, ?_⟩
  intro M hM u₀ hu₀ hclose
  obtain ⟨u, σ, hu, hσ, hrest⟩ := hmain M hM u₀ hu₀ hclose
  exact ⟨u, σ, hR u hu, hV σ hσ, hrest⟩

/-- Comparator-facing form of the proof. The default proof arguments are elaborated
in the calling context: `h₁`, `h₂`, and `h₃` are the hypotheses in the copied
challenge statement. They perform the record conversions without requiring any
arguments at the use site. The spectral gap determines the copied resolvent
predicate before its equivalence is synthesized. -/
theorem vHJ_approximates_planar_front_solution
    {f : ℝ^n → ℝ^n} {D : ℝ^n →L[ℝ] ℝ^n} {c : ℝ} {φ ψ : ℝ → ℝ^n}
    {P : ℝ → ℂ → (ℝ → ℂ^n) → (ℝ → ℂ^n) → Prop}
    {R : (ℝ → ℝ^d → ℝ^n) → Prop}
    {V : (ℝ → ℝ^(d - 1) → ℝ) → Prop}
    (hn : 1 ≤ n := by assumption) (hd : 2 ≤ d := by assumption)
    (hpar : IsSmoothParabolic f D := by exact ⟨h₁.smooth, h₁.positive, h₁.kernel⟩)
    (hfront : IsSmoothFront f D c φ := by exact ⟨h₂.smooth, h₂.ode, h₂.endpoints⟩)
    (hintegrable : Integrable ψ := by exact h₃.integrable)
    (hnormalized : ∫ x, ⟪ψ x, deriv φ x⟫_ℝ = 1 := by exact h₃.normalized)
    (hgap : ∃ θ > 0, ∀ l ∈ compl {l | ∀ w, IsBUC w → ∃! v, P 0 l v w},
      l = 0 ∨ l.re ≤ -θ := by exact h₃.horizontal_spectral_gap)
    (hkernel : ∀ v, P 0 0 v 0 ↔ ∃ a : ℂ, ∀ x, v x = a • embed (deriv φ x) :=
      by exact h₃.horizontal_kernel)
    (hsolvability : ∀ w, IsBUC w →
      (∫ z, ⟪embed (ψ z), w z⟫_ℂ = 0 ↔ ∃ v, P 0 0 v w) :=
      by exact h₃.horizontal_solvability)
    (hlow : d_perp D φ ψ > 0 := by exact h₃.transverse_low_wavenumber)
    (hhigh : ∀ k₀ > 0, ∃ θ₁ > 0, ∀ k ≥ k₀,
      ∀ l ∈ compl {l | ∀ w, IsBUC w → ∃! v, P k l v w}, l.re ≤ -θ₁ :=
      by exact h₃.transverse_high_wavenumber)
    (hP : ∀ k l v w, P k l v w ↔ IsTransverseResolventSolution f D c φ k l v w := by
      intro k l v w
      exact ⟨fun h ↦ ⟨h.smooth, h.buc, h.pde⟩, fun h ↦ ⟨h.smooth, h.buc, h.pde⟩⟩)
    (hR : ∀ u, IsRDESolution f D u → R u := by
      intro u h
      exact ⟨h.cont, h.smooth, h.pde⟩)
    (hV : ∀ σ, IsVHJSolution c σ (d_perp D φ ψ) → V σ := by
      intro σ h
      exact ⟨h.cont, h.smooth, h.pde⟩) :
    ∃ C > 0, ∃ ε > 0, ∀ E_0 ∈ Icc 0 ε, ∀ u₀ : ℝ^d → ℝ^n,
      IsBUC u₀ → IsCloseToFront φ u₀ E_0 →
      ∃ u σ, R u ∧ V σ ∧
        u 0 = u₀ ∧ (∀ y, σ 0 y = ∫ z, ⟪ψ z, φ z - u 0 (full y z)⟫_ℝ) ∧
        ∀ t ≥ 0, ∀ x, ‖u t x - φ (horizontal x - c * t - σ t (transverse x))‖ ≤
          C * E_0 * (E_0 + (1 + t)⁻¹ * Real.log (2 + t)) :=
  vHJ_approximates_planar_front_of_equivalent_predicates f D c φ ψ hn hd hP hR hV
    hpar hfront hintegrable hnormalized hgap hkernel hsolvability hlow hhigh

end

end Planarwave
