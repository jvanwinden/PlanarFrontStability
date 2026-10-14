/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

/-!
# Twice differentiable bounded uniformly continuous functions

The longitudinal operators in Section 2 of the paper have the common domain
`BUC²(ℝ, ℂⁿ)`.  This file realizes that graph domain as the closed subspace of triples
`(v, v', v'')` of BUC functions satisfying the two derivative identities.  Its inherited product
norm is equivalent to the usual graph norm, and closedness gives completeness.
-/

open Filter Function Set

universe u

noncomputable section

namespace Planarwave

variable (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The ambient space of a function and its first two proposed derivatives. -/
abbrev BUC2Jet := (BUC ℝ F × BUC ℝ F) × BUC ℝ F

/-- The linear subspace of BUC jets satisfying the two derivative identities. -/
def buc2Submodule : Submodule ℝ (BUC2Jet F) where
  carrier p := ∀ x,
    HasDerivAt (p.1.1 : ℝ → F) (p.1.2 x) x ∧
    HasDerivAt (p.1.2 : ℝ → F) (p.2 x) x
  zero_mem' := by
    intro x
    constructor <;> simpa using (hasDerivAt_const x (0 : F))
  add_mem' := by
    intro p q hp hq x
    exact ⟨(hp x).1.add (hq x).1, (hp x).2.add (hq x).2⟩
  smul_mem' := by
    intro c p hp x
    exact ⟨(hp x).1.const_smul c, (hp x).2.const_smul c⟩

/-- The carrier of `buc2Submodule` is closed under uniform convergence of a function and its first
two derivatives. -/
theorem isClosed_buc2Submodule : IsClosed (buc2Submodule F : Set (BUC2Jet F)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u p hu hup
  have h0 : Tendsto (fun n ↦ (u n).1.1) atTop (nhds p.1.1) := by
    have hc : Continuous (fun q : BUC2Jet F ↦ q.1.1) := by fun_prop
    exact (hc.tendsto p).comp hup
  have h1 : Tendsto (fun n ↦ (u n).1.2) atTop (nhds p.1.2) := by
    have hc : Continuous (fun q : BUC2Jet F ↦ q.1.2) := by fun_prop
    exact (hc.tendsto p).comp hup
  have h2 : Tendsto (fun n ↦ (u n).2) atTop (nhds p.2) := by
    have hc : Continuous (fun q : BUC2Jet F ↦ q.2) := by fun_prop
    exact (hc.tendsto p).comp hup
  have h0u : TendstoUniformly (fun n ↦ ((u n).1.1 : ℝ → F)) p.1.1 atTop :=
    BUC.tendsto_iff_tendstoUniformly.mp h0
  have h1u : TendstoUniformly (fun n ↦ ((u n).1.2 : ℝ → F)) p.1.2 atTop :=
    BUC.tendsto_iff_tendstoUniformly.mp h1
  have h2u : TendstoUniformly (fun n ↦ ((u n).2 : ℝ → F)) p.2 atTop :=
    BUC.tendsto_iff_tendstoUniformly.mp h2
  intro x
  constructor
  · exact hasDerivAt_of_tendstoUniformly h1u
      (Eventually.of_forall fun n y ↦ (hu n y).1)
      (fun y ↦ h0u.tendsto_at y) x
  · exact hasDerivAt_of_tendstoUniformly h2u
      (Eventually.of_forall fun n y ↦ (hu n y).2)
      (fun y ↦ h1u.tendsto_at y) x

/-- The Banach graph domain `BUC²(ℝ,F)`. -/
abbrev BUC2 := buc2Submodule F

noncomputable instance : CompleteSpace (BUC2 F) := by
  letI : IsClosed (buc2Submodule F : Set (BUC2Jet F)) := isClosed_buc2Submodule F
  infer_instance

namespace BUC2

/-- The underlying BUC function. -/
def value (v : BUC2 F) : BUC ℝ F := v.1.1.1

/-- The bundled first derivative. -/
def deriv (v : BUC2 F) : BUC ℝ F := v.1.1.2

/-- The bundled second derivative. -/
def deriv2 (v : BUC2 F) : BUC ℝ F := v.1.2

instance : FunLike (BUC2 F) ℝ F where
  coe v := value F v
  coe_injective v w h := by
    have hval : v.1.1.1 = w.1.1.1 := BUC.ext fun x ↦ congrFun h x
    have hderiv : v.1.1.2 = w.1.1.2 := by
      apply BUC.ext
      intro x
      apply (v.property x).1.unique
      rw [hval]
      exact (w.property x).1
    have hderiv2 : v.1.2 = w.1.2 := by
      apply BUC.ext
      intro x
      apply (v.property x).2.unique
      rw [hderiv]
      exact (w.property x).2
    apply Subtype.ext
    exact Prod.ext (Prod.ext hval hderiv) hderiv2

@[simp]
theorem value_apply (v : BUC2 F) (x : ℝ) : BUC2.value F v x = v x := rfl

theorem hasDerivAt_value (v : BUC2 F) (x : ℝ) :
    HasDerivAt (v : ℝ → F) (BUC2.deriv F v x) x := v.property x |>.1

theorem hasDerivAt_deriv (v : BUC2 F) (x : ℝ) :
    HasDerivAt (BUC2.deriv F v : ℝ → F) (BUC2.deriv2 F v x) x := v.property x |>.2

@[simp]
theorem deriv_eq (v : BUC2 F) (x : ℝ) :
    _root_.deriv (v : ℝ → F) x = BUC2.deriv F v x :=
  (hasDerivAt_value F v x).deriv

@[simp]
theorem second_deriv_eq (v : BUC2 F) (x : ℝ) :
    _root_.deriv (_root_.deriv (v : ℝ → F)) x = BUC2.deriv2 F v x := by
  have hfun : _root_.deriv (v : ℝ → F) = BUC2.deriv F v :=
    funext (deriv_eq F v)
  rw [hfun]
  exact (hasDerivAt_deriv F v x).deriv

/-- Inclusion of the graph domain into longitudinal BUC. -/
def valueCLM : BUC2 F →L[ℝ] BUC ℝ F :=
  ((ContinuousLinearMap.fst ℝ (BUC ℝ F) (BUC ℝ F)).comp
    (ContinuousLinearMap.fst ℝ (BUC ℝ F × BUC ℝ F) (BUC ℝ F))).comp
      (buc2Submodule F).subtypeL

/-- First derivative as a continuous linear map out of the graph domain. -/
def derivCLM : BUC2 F →L[ℝ] BUC ℝ F :=
  ((ContinuousLinearMap.snd ℝ (BUC ℝ F) (BUC ℝ F)).comp
    (ContinuousLinearMap.fst ℝ (BUC ℝ F × BUC ℝ F) (BUC ℝ F))).comp
      (buc2Submodule F).subtypeL

/-- Second derivative as a continuous linear map out of the graph domain. -/
def deriv2CLM : BUC2 F →L[ℝ] BUC ℝ F :=
  (ContinuousLinearMap.snd ℝ (BUC ℝ F × BUC ℝ F) (BUC ℝ F)).comp
    (buc2Submodule F).subtypeL

@[simp] theorem valueCLM_apply (v : BUC2 F) : valueCLM F v = BUC2.value F v := rfl
@[simp] theorem derivCLM_apply (v : BUC2 F) : derivCLM F v = BUC2.deriv F v := rfl
@[simp] theorem deriv2CLM_apply (v : BUC2 F) : deriv2CLM F v = BUC2.deriv2 F v := rfl

theorem valueCLM_injective : Injective (valueCLM F) := by
  intro v w h
  apply DFunLike.coe_injective
  funext x
  exact congrArg (fun g : BUC ℝ F ↦ g x) h

end BUC2

end Planarwave
