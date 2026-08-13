/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/

module

public import Mathlib

public section

/-!
# The scalar Cole--Hopf transform

This file formalizes the scalar change of variables from (5.3) of the cited paper.  The parameter
`β` is allowed to vanish, in which case both the transform and its inverse are defined to be the
identity.  For nonzero `β`, the range is the interval `β * x > -1` on which the logarithmic inverse
is defined.
-/

open Set
open scoped ContDiff

namespace Planarwave

section ColeHopf

/-- The scalar Cole--Hopf transform `Ψ_β(s) = (exp (βs) - 1) / β`, continuously extended at
`β = 0` by the identity. -/
noncomputable def coleHopf (β s : ℝ) : ℝ :=
  if β = 0 then s else (Real.exp (β * s) - 1) / β

/-- The natural range of `coleHopf β`. -/
def coleHopfDomain (β : ℝ) : Set ℝ := {x | -1 < β * x}

/-- The logarithmic inverse of the scalar Cole--Hopf transform, continuously extended at `β = 0`
by the identity.  Its inverse laws are stated on `coleHopfDomain β`. -/
noncomputable def coleHopfInv (β x : ℝ) : ℝ :=
  if β = 0 then x else Real.log (1 + β * x) / β

@[simp]
theorem coleHopf_zero (s : ℝ) : coleHopf 0 s = s := by
  simp [coleHopf]

theorem coleHopf_of_ne {β : ℝ} (hβ : β ≠ 0) (s : ℝ) :
    coleHopf β s = (Real.exp (β * s) - 1) / β := by
  simp [coleHopf, hβ]

@[simp]
theorem coleHopf_zero_apply (β : ℝ) : coleHopf β 0 = 0 := by
  by_cases hβ : β = 0
  · simp [hβ]
  · simp [coleHopf_of_ne hβ]

@[simp]
theorem coleHopfInv_zero (x : ℝ) : coleHopfInv 0 x = x := by
  simp [coleHopfInv]

theorem coleHopfInv_of_ne {β : ℝ} (hβ : β ≠ 0) (x : ℝ) :
    coleHopfInv β x = Real.log (1 + β * x) / β := by
  simp [coleHopfInv, hβ]

@[simp]
theorem coleHopfInv_zero_apply (β : ℝ) : coleHopfInv β 0 = 0 := by
  by_cases hβ : β = 0
  · simp [hβ]
  · simp [coleHopfInv_of_ne hβ]

@[simp]
theorem mem_coleHopfDomain {β x : ℝ} : x ∈ coleHopfDomain β ↔ -1 < β * x := Iff.rfl

@[simp]
theorem coleHopfDomain_zero : coleHopfDomain 0 = univ := by
  ext x
  simp [coleHopfDomain]

/-- The key algebraic identity behind the Cole--Hopf change of variables. -/
theorem one_add_mul_coleHopf (β s : ℝ) :
    1 + β * coleHopf β s = Real.exp (β * s) := by
  by_cases hβ : β = 0
  · simp [hβ]
  · rw [coleHopf_of_ne hβ]
    field_simp
    ring

theorem mul_coleHopf (β s : ℝ) :
    β * coleHopf β s = Real.exp (β * s) - 1 := by
  linarith [one_add_mul_coleHopf β s]

/-- The Cole--Hopf transform always lands in its logarithmic inverse's domain. -/
theorem coleHopf_mem_domain (β s : ℝ) : coleHopf β s ∈ coleHopfDomain β := by
  rw [mem_coleHopfDomain]
  have hexp := Real.exp_pos (β * s)
  rw [← one_add_mul_coleHopf] at hexp
  linarith

/-- Applying the logarithmic inverse after the Cole--Hopf transform gives the identity. -/
@[simp]
theorem coleHopfInv_coleHopf (β s : ℝ) : coleHopfInv β (coleHopf β s) = s := by
  by_cases hβ : β = 0
  · simp [hβ]
  · rw [coleHopfInv_of_ne hβ, one_add_mul_coleHopf, Real.log_exp]
    apply (div_eq_iff hβ).2
    ring

/-- Applying the Cole--Hopf transform after its logarithmic inverse gives the identity on the
natural positive domain. -/
@[simp]
theorem coleHopf_coleHopfInv {β x : ℝ} (hx : x ∈ coleHopfDomain β) :
    coleHopf β (coleHopfInv β x) = x := by
  by_cases hβ : β = 0
  · simp [hβ]
  · rw [coleHopf_of_ne hβ, coleHopfInv_of_ne hβ]
    have hpos : 0 < 1 + β * x := by
      rw [mem_coleHopfDomain] at hx
      linarith
    have harg : β * (Real.log (1 + β * x) / β) = Real.log (1 + β * x) := by
      field_simp
    rw [harg, Real.exp_log hpos]
    field_simp
    ring

theorem exp_mul_coleHopfInv {β x : ℝ} (hx : x ∈ coleHopfDomain β) :
    Real.exp (β * coleHopfInv β x) = 1 + β * x := by
  rw [← one_add_mul_coleHopf, coleHopf_coleHopfInv hx]

/-- The paper's bijection `Ψ_β : ℝ → {x | βx > -1}`. -/
@[expose] noncomputable def coleHopfEquiv (β : ℝ) : ℝ ≃ {x // x ∈ coleHopfDomain β} where
  toFun s := ⟨coleHopf β s, coleHopf_mem_domain β s⟩
  invFun x := coleHopfInv β x
  left_inv := coleHopfInv_coleHopf β
  right_inv x := Subtype.ext (coleHopf_coleHopfInv x.property)

@[simp]
theorem coleHopfEquiv_apply (β s : ℝ) : (coleHopfEquiv β s : ℝ) = coleHopf β s := rfl

@[simp]
theorem coleHopfEquiv_symm_apply (β : ℝ) (x : {x // x ∈ coleHopfDomain β}) :
    (coleHopfEquiv β).symm x = coleHopfInv β x := rfl

/-- `coleHopf β` is smooth for every value of `β`, including `β = 0`. -/
theorem contDiff_coleHopf (β : ℝ) : ContDiff ℝ ∞ (coleHopf β) := by
  by_cases hβ : β = 0
  · subst β
    rw [show coleHopf 0 = id by
      funext x
      simp]
    exact contDiff_id
  · rw [show coleHopf β = fun s => (Real.exp (β * s) - 1) / β by
      funext s
      exact coleHopf_of_ne hβ s]
    fun_prop

/-- First derivative of the Cole--Hopf transform. -/
theorem hasDerivAt_coleHopf (β s : ℝ) :
    HasDerivAt (coleHopf β) (Real.exp (β * s)) s := by
  by_cases hβ : β = 0
  · subst β
    rw [show coleHopf 0 = id by
      funext x
      simp]
    simpa using hasDerivAt_id s
  · rw [show coleHopf β = fun x => (Real.exp (β * x) - 1) / β by
      funext x
      exact coleHopf_of_ne hβ x]
    have hlin : HasDerivAt (fun x : ℝ => β * x) β s := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul β
    simpa [hβ] using ((hlin.exp.sub_const 1).div_const β)

@[simp]
theorem deriv_coleHopf (β s : ℝ) : deriv (coleHopf β) s = Real.exp (β * s) :=
  (hasDerivAt_coleHopf β s).deriv

theorem deriv_coleHopf_eq_one_add (β s : ℝ) :
    deriv (coleHopf β) s = 1 + β * coleHopf β s := by
  rw [deriv_coleHopf, one_add_mul_coleHopf]

/-- The scalar Cole--Hopf transform is strictly increasing for every `β`. -/
theorem strictMono_coleHopf (β : ℝ) : StrictMono (coleHopf β) := by
  apply strictMono_of_deriv_pos
  intro s
  rw [deriv_coleHopf]
  exact Real.exp_pos _

/-- On `[-R,R]`, the Cole--Hopf transform has Lipschitz constant `exp (|β| R)`. -/
theorem lipschitzOnWith_coleHopf_Icc (β R : ℝ) (_hR : 0 ≤ R) :
    LipschitzOnWith (Real.toNNReal (Real.exp (|β| * R)))
      (coleHopf β) (Icc (-R) R) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro s _hs
    exact (hasDerivAt_coleHopf β s).differentiableAt
  · intro s hs
    have habs : |s| ≤ R := abs_le.2 hs
    have harg : β * s ≤ |β| * R := by
      calc
        β * s ≤ |β * s| := le_abs_self _
        _ = |β| * |s| := abs_mul β s
        _ ≤ |β| * R := mul_le_mul_of_nonneg_left habs (abs_nonneg β)
    rw [deriv_coleHopf]
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr harg
  · exact convex_Icc (-R) R

/-- A uniform first-order bound near the origin. -/
theorem abs_coleHopf_le_two_mul_abs {β s : ℝ} (hsmall : |β * s| ≤ 1) :
    |coleHopf β s| ≤ 2 * |s| := by
  by_cases hβ : β = 0
  · subst β
    simp
    nlinarith [abs_nonneg s]
  · rw [coleHopf_of_ne hβ, abs_div]
    have hexp := Real.abs_exp_sub_one_le hsmall
    apply (div_le_iff₀ (abs_pos.2 hβ)).2
    calc
      |Real.exp (β * s) - 1| ≤ 2 * |β * s| := hexp
      _ = (2 * |s|) * |β| := by rw [abs_mul]; ring

/-- Quadratic error of the Cole--Hopf transform from the identity near the origin. -/
theorem abs_coleHopf_sub_self_le {β s : ℝ} (hsmall : |β * s| ≤ 1) :
    |coleHopf β s - s| ≤ |β| * s ^ 2 := by
  by_cases hβ : β = 0
  · subst β
    simp
  · rw [coleHopf_of_ne hβ]
    have hrearrange :
        (Real.exp (β * s) - 1) / β - s =
          (Real.exp (β * s) - 1 - β * s) / β := by
      field_simp
    rw [hrearrange, abs_div]
    apply (div_le_iff₀ (abs_pos.2 hβ)).2
    calc
      |Real.exp (β * s) - 1 - β * s| ≤ (β * s) ^ 2 :=
        Real.abs_exp_sub_one_sub_id_le hsmall
      _ = (|β| * s ^ 2) * |β| := by
        rw [mul_pow, ← sq_abs]
        ring

/-- Second derivative of the Cole--Hopf transform. -/
theorem second_deriv_coleHopf (β s : ℝ) :
    deriv (deriv (coleHopf β)) s = β * Real.exp (β * s) := by
  have hfun : deriv (coleHopf β) = fun x => Real.exp (β * x) := by
    funext x
    exact deriv_coleHopf β x
  rw [hfun]
  have hlin : HasDerivAt (fun x : ℝ => β * x) β s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul β
  simpa only [mul_comm] using hlin.exp.deriv

/-- Chain rule in the form used when transforming the viscous Hamilton--Jacobi equation. -/
theorem HasDerivAt.coleHopf {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (β : ℝ) :
    HasDerivAt (fun y => coleHopf β (f y)) (Real.exp (β * f x) * f') x :=
  (hasDerivAt_coleHopf β (f x)).comp x hf

/-- Derivative of the logarithmic inverse on its natural domain. -/
theorem hasDerivAt_coleHopfInv {β x : ℝ} (hx : x ∈ coleHopfDomain β) :
    HasDerivAt (coleHopfInv β) (1 + β * x)⁻¹ x := by
  by_cases hβ : β = 0
  · subst β
    rw [show coleHopfInv 0 = id by
      funext y
      simp]
    simpa using hasDerivAt_id x
  · rw [show coleHopfInv β = fun y => Real.log (1 + β * y) / β by
      funext y
      exact coleHopfInv_of_ne hβ y]
    have hpos : 0 < 1 + β * x := by
      rw [mem_coleHopfDomain] at hx
      linarith
    have hlin : HasDerivAt (fun y : ℝ => β * y) β x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul β
    have haff : HasDerivAt (fun y : ℝ => 1 + β * y) β x := hlin.const_add 1
    have hraw := (haff.log hpos.ne').div_const β
    have hcoef : (β / (1 + β * x)) / β = (1 + β * x)⁻¹ := by
      field_simp
    rw [← hcoef]
    exact hraw

@[simp]
theorem deriv_coleHopfInv {β x : ℝ} (hx : x ∈ coleHopfDomain β) :
    deriv (coleHopfInv β) x = (1 + β * x)⁻¹ :=
  (hasDerivAt_coleHopfInv hx).deriv

/-- The logarithmic inverse is smooth on the open interval `βx > -1`. -/
theorem contDiffOn_coleHopfInv (β : ℝ) :
    ContDiffOn ℝ ∞ (coleHopfInv β) (coleHopfDomain β) := by
  intro x hx
  by_cases hβ : β = 0
  · subst β
    rw [show coleHopfInv 0 = id by
      funext y
      simp]
    exact
      (contDiffAt_id (𝕜 := ℝ) (x := x) : ContDiffAt ℝ ∞ (id : ℝ → ℝ) x).contDiffWithinAt
  · rw [show coleHopfInv β = fun y => Real.log (1 + β * y) / β by
      funext y
      exact coleHopfInv_of_ne hβ y]
    have hpos : 0 < 1 + β * x := by
      rw [mem_coleHopfDomain] at hx
      linarith
    have haff : ContDiffAt ℝ ∞ (fun y : ℝ => 1 + β * y) x := by fun_prop
    exact ((haff.log hpos.ne').div_const β).contDiffWithinAt

end ColeHopf

end Planarwave
