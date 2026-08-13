/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC2
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# The complex longitudinal graph domain

The Fourier symbols in Sections 2--3 act complex-linearly.  This file equips the same closed
`(v,v',v'')` carrier used by `BUC2` with its natural complex submodule structure.
-/

open Function Set

universe u

noncomputable section

namespace Planarwave

variable (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [SMulCommClass ℝ ℂ F] [CompleteSpace F]

/-- The complex-linear subspace of BUC jets satisfying the derivative identities. -/
def complexBUC2Submodule : Submodule ℂ (BUC2Jet F) where
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

theorem isClosed_complexBUC2Submodule :
    IsClosed (complexBUC2Submodule F : Set (BUC2Jet F)) := by
  change IsClosed (buc2Submodule F : Set (BUC2Jet F))
  exact isClosed_buc2Submodule F

/-- The complex Banach graph domain `BUC²(ℝ,F)`. -/
abbrev ComplexBUC2 := complexBUC2Submodule F

noncomputable instance : CompleteSpace (ComplexBUC2 F) := by
  letI : IsClosed (complexBUC2Submodule F : Set (BUC2Jet F)) :=
    isClosed_complexBUC2Submodule F
  infer_instance

namespace ComplexBUC2

def value (v : ComplexBUC2 F) : BUC ℝ F := v.1.1.1
def deriv (v : ComplexBUC2 F) : BUC ℝ F := v.1.1.2
def deriv2 (v : ComplexBUC2 F) : BUC ℝ F := v.1.2

instance : FunLike (ComplexBUC2 F) ℝ F where
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

@[simp] theorem value_apply (v : ComplexBUC2 F) (x : ℝ) : value F v x = v x := rfl

theorem hasDerivAt_value (v : ComplexBUC2 F) (x : ℝ) :
    HasDerivAt (v : ℝ → F) (deriv F v x) x := (v.property x).1

theorem hasDerivAt_deriv (v : ComplexBUC2 F) (x : ℝ) :
    HasDerivAt (deriv F v : ℝ → F) (deriv2 F v x) x := (v.property x).2

@[simp] theorem deriv_eq (v : ComplexBUC2 F) (x : ℝ) :
    _root_.deriv (v : ℝ → F) x = deriv F v x := (hasDerivAt_value F v x).deriv

@[simp] theorem second_deriv_eq (v : ComplexBUC2 F) (x : ℝ) :
    _root_.deriv (_root_.deriv (v : ℝ → F)) x = deriv2 F v x := by
  have hfun : _root_.deriv (v : ℝ → F) = deriv F v := funext (deriv_eq F v)
  rw [hfun]
  exact (hasDerivAt_deriv F v x).deriv

/-- Complex-linear inclusion into longitudinal BUC. -/
def valueCLM : ComplexBUC2 F →L[ℂ] BUC ℝ F :=
  ((ContinuousLinearMap.fst ℂ (BUC ℝ F) (BUC ℝ F)).comp
    (ContinuousLinearMap.fst ℂ (BUC ℝ F × BUC ℝ F) (BUC ℝ F))).comp
      (complexBUC2Submodule F).subtypeL

def derivCLM : ComplexBUC2 F →L[ℂ] BUC ℝ F :=
  ((ContinuousLinearMap.snd ℂ (BUC ℝ F) (BUC ℝ F)).comp
    (ContinuousLinearMap.fst ℂ (BUC ℝ F × BUC ℝ F) (BUC ℝ F))).comp
      (complexBUC2Submodule F).subtypeL

def deriv2CLM : ComplexBUC2 F →L[ℂ] BUC ℝ F :=
  (ContinuousLinearMap.snd ℂ (BUC ℝ F × BUC ℝ F) (BUC ℝ F)).comp
    (complexBUC2Submodule F).subtypeL

@[simp] theorem valueCLM_apply (v : ComplexBUC2 F) : valueCLM F v = value F v := rfl
@[simp] theorem derivCLM_apply (v : ComplexBUC2 F) : derivCLM F v = deriv F v := rfl
@[simp] theorem deriv2CLM_apply (v : ComplexBUC2 F) : deriv2CLM F v = deriv2 F v := rfl

theorem valueCLM_injective : Injective (valueCLM F) := by
  intro v w h
  apply DFunLike.coe_injective
  funext x
  exact congrArg (fun g : BUC ℝ F ↦ g x) h

end ComplexBUC2

end Planarwave
