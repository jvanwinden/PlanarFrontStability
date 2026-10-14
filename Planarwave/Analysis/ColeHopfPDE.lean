/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/

module

public import Planarwave.Analysis.ColeHopfLaplacian

public section

/-!
# Cole--Hopf cancellation for the forced viscous Hamilton--Jacobi equation

This file isolates the pointwise calculation used in Section 5 of the cited paper.  Suppose

`∂ₜσ = dPerp * Δσ + (c / 2) * ‖∇σ‖² - g`

and choose `β` so that `dPerp * β = c / 2`.  Then `exp (β * σ)` solves the forced heat equation

`∂ₜ exp (βσ) = dPerp * Δ exp (βσ) - β * exp (βσ) * g`.

We also record the equivalent identity for the normalized transform `coleHopf β σ`, whose forcing
is `-exp (βσ) * g`.  The proofs retain the time and space chain rules as separate steps and use
only the final algebraic relation `dPerp * β = c / 2` for the cancellation.
-/

open Function
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

namespace Planarwave

section SpatialExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The spatial Laplacian chain rule for the exponential form of the Cole--Hopf transform. -/
theorem laplacian_exp_mul_comp_apply (β : ℝ) (σ : E → ℝ)
    (hσ : ContDiff ℝ 2 σ) (x : E) :
    Δ (fun y => Real.exp (β * σ y)) x =
      β * Real.exp (β * σ x) * (Δ σ x + β * ‖∇ σ x‖ ^ 2) := by
  have h2top : (2 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hcole : ContDiffAt ℝ 2 (coleHopf β ∘ σ) x :=
    (((contDiff_coleHopf β).of_le h2top).comp hσ).contDiffAt
  have hconst : ContDiffAt ℝ 2 (fun _ : E => (1 : ℝ)) x := contDiffAt_const
  have hscaled : ContDiffAt ℝ 2 (β • (coleHopf β ∘ σ)) x := by
    fun_prop
  have hexp : (fun y => Real.exp (β * σ y)) =
      (fun _ : E => (1 : ℝ)) + β • (coleHopf β ∘ σ) := by
    funext y
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, comp_apply] using
      (one_add_mul_coleHopf β (σ y)).symm
  rw [hexp, hconst.laplacian_add hscaled,
    InnerProductSpace.laplacian_const,
    InnerProductSpace.laplacian_smul β hcole]
  simp only [Pi.zero_apply, zero_add, smul_eq_mul]
  rw [laplacian_coleHopf_comp_apply β σ hσ x]
  ring

end SpatialExponential

section PointwiseCancellation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Pointwise forced viscous Hamilton--Jacobi cancellation for the normalized Cole--Hopf
transform. -/
theorem hasDerivAt_coleHopf_of_forced_vHJ
    (σ : ℝ → E → ℝ) (t : ℝ) (x : E) (σt dPerp c β g : ℝ)
    (htime : HasDerivAt (fun s => σ s x) σt t)
    (hspace : ContDiff ℝ 2 (σ t))
    (hcancel : dPerp * β = c / 2)
    (hpde : σt = dPerp * Δ (σ t) x + (c / 2) * ‖∇ (σ t) x‖ ^ 2 - g) :
    HasDerivAt (fun s => coleHopf β (σ s x))
      (dPerp * Δ (coleHopf β ∘ σ t) x - Real.exp (β * σ t x) * g) t := by
  convert HasDerivAt.coleHopf htime β using 1
  rw [hpde, laplacian_coleHopf_comp_apply β (σ t) hspace x, ← hcancel]
  ring

/-- Pointwise forced heat equation for `exp (β * σ)`. -/
theorem hasDerivAt_exp_mul_of_forced_vHJ
    (σ : ℝ → E → ℝ) (t : ℝ) (x : E) (σt dPerp c β g : ℝ)
    (htime : HasDerivAt (fun s => σ s x) σt t)
    (hspace : ContDiff ℝ 2 (σ t))
    (hcancel : dPerp * β = c / 2)
    (hpde : σt = dPerp * Δ (σ t) x + (c / 2) * ‖∇ (σ t) x‖ ^ 2 - g) :
    HasDerivAt (fun s => Real.exp (β * σ s x))
      (dPerp * Δ (fun y => Real.exp (β * σ t y)) x -
        β * Real.exp (β * σ t x) * g) t := by
  have htransform := (htime.const_mul β).exp
  convert htransform using 1
  rw [hpde, laplacian_exp_mul_comp_apply β (σ t) hspace x, ← hcancel]
  ring

end PointwiseCancellation

section FieldCancellation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end FieldCancellation

section InverseCancellation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Conversely, the inverse normalized Cole--Hopf transform of a classical heat solution
satisfies the viscous Hamilton--Jacobi equation. This includes `c = β = 0`. -/
theorem hasDerivAt_coleHopfInv_of_heat
    (w : ℝ → E → ℝ) (t : ℝ) (x : E) (a c β : ℝ)
    (htime : HasDerivAt (fun s => w s x) (a * Δ (w t) x) t)
    (hspace : ContDiff ℝ 2 (w t))
    (hdomain : ∀ y, w t y ∈ coleHopfDomain β)
    (hcancel : a * β = c / 2) :
    HasDerivAt (fun s => coleHopfInv β (w s x))
      (a * Δ (coleHopfInv β ∘ w t) x +
        (c / 2) * ‖∇ (coleHopfInv β ∘ w t) x‖ ^ 2) t := by
  let σ : E → ℝ := coleHopfInv β ∘ w t
  have hσ : ContDiff ℝ 2 σ := by
    rw [← contDiffOn_univ]
    apply ((contDiffOn_coleHopfInv β).of_le (show (2 : ℕ∞ω) ≤ ∞ from
      WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).comp
      hspace.contDiffOn
    intro y _
    exact hdomain y
  have htransform : coleHopf β ∘ σ = w t := by
    funext y
    exact coleHopf_coleHopfInv (hdomain y)
  have hlap := laplacian_coleHopf_comp_apply β σ hσ x
  rw [htransform] at hlap
  have hderiv := (hasDerivAt_coleHopfInv (hdomain x)).comp t htime
  have hexp : 1 + β * w t x = Real.exp (β * σ x) :=
    (exp_mul_coleHopfInv (hdomain x)).symm
  have hcoef : (1 + β * w t x)⁻¹ * (a * Δ (w t) x) =
      a * Δ σ x + (c / 2) * ‖∇ σ x‖ ^ 2 := by
    rw [hexp, hlap, ← hcancel]
    field_simp
  rw [hcoef] at hderiv
  exact hderiv

end InverseCancellation

end Planarwave
