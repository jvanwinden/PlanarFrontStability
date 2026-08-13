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

/-- The preceding forced heat equation with the exponential factor rewritten as
`1 + β * coleHopf β σ`. -/
theorem hasDerivAt_coleHopf_of_forced_vHJ_eq_one_add
    (σ : ℝ → E → ℝ) (t : ℝ) (x : E) (σt dPerp c β g : ℝ)
    (htime : HasDerivAt (fun s => σ s x) σt t)
    (hspace : ContDiff ℝ 2 (σ t))
    (hcancel : dPerp * β = c / 2)
    (hpde : σt = dPerp * Δ (σ t) x + (c / 2) * ‖∇ (σ t) x‖ ^ 2 - g) :
    HasDerivAt (fun s => coleHopf β (σ s x))
      (dPerp * Δ (coleHopf β ∘ σ t) x -
        (1 + β * coleHopf β (σ t x)) * g) t := by
  rw [one_add_mul_coleHopf]
  exact hasDerivAt_coleHopf_of_forced_vHJ σ t x σt dPerp c β g
    htime hspace hcancel hpde

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

/-- The paper's parameter choice `β = c / (2 * dPerp)` satisfies the cancellation relation when
the transverse diffusivity is nonzero. -/
theorem hasDerivAt_exp_mul_c_div_two_mul_of_forced_vHJ
    (σ : ℝ → E → ℝ) (t : ℝ) (x : E) (σt dPerp c g : ℝ)
    (hdPerp : dPerp ≠ 0)
    (htime : HasDerivAt (fun s => σ s x) σt t)
    (hspace : ContDiff ℝ 2 (σ t))
    (hpde : σt = dPerp * Δ (σ t) x + (c / 2) * ‖∇ (σ t) x‖ ^ 2 - g) :
    HasDerivAt (fun s => Real.exp ((c / (2 * dPerp)) * σ s x))
      (dPerp * Δ (fun y => Real.exp ((c / (2 * dPerp)) * σ t y)) x -
        (c / (2 * dPerp)) * Real.exp ((c / (2 * dPerp)) * σ t x) * g) t := by
  apply hasDerivAt_exp_mul_of_forced_vHJ σ t x σt dPerp c (c / (2 * dPerp)) g
    htime hspace
  · field_simp
  · exact hpde

end PointwiseCancellation

section FieldCancellation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Forced heat equation at a fixed time, stated as an equality of spatial scalar fields.  The
function `σt` supplies the explicitly assumed time derivative of `σ`. -/
theorem deriv_exp_mul_of_forced_vHJ
    (σ : ℝ → E → ℝ) (σt g : E → ℝ) (t dPerp c β : ℝ)
    (htime : ∀ x, HasDerivAt (fun s => σ s x) (σt x) t)
    (hspace : ContDiff ℝ 2 (σ t))
    (hcancel : dPerp * β = c / 2)
    (hpde : ∀ x,
      σt x = dPerp * Δ (σ t) x + (c / 2) * ‖∇ (σ t) x‖ ^ 2 - g x) :
    (fun x => deriv (fun s => Real.exp (β * σ s x)) t) =
      fun x => dPerp * Δ (fun y => Real.exp (β * σ t y)) x -
        β * Real.exp (β * σ t x) * g x := by
  funext x
  exact (hasDerivAt_exp_mul_of_forced_vHJ σ t x (σt x) dPerp c β (g x)
    (htime x) hspace hcancel (hpde x)).deriv

end FieldCancellation

end Planarwave
