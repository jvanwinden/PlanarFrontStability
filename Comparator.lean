/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Challenge
import all Solution
import Mathlib.Util.AssertNoSorry

/-!
# Challenge/solution comparator

Check that the proved theorem has exactly the type of the original challenge,
and report the axioms used by the new proof. Reading the original theorem's
type here does not use its admitted proof as a mathematical premise.
Run `lake build Comparator` to rebuild and check both files, or
`lake env lean Comparator.lean` after their dependencies have been built.
-/

open Lean Elab Command in
run_cmd do
  let expected := (← getConstInfo ``vHJ_approximates_planar_front).type
  let actual := (← getConstInfo ``Planarwave.vHJ_approximates_planar_front_proved).type
  unless ← liftTermElabM (Lean.Meta.isDefEq expected actual) do
    throwError "The new proof does not have the unchanged challenge's exact type."
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms ``Planarwave.vHJ_approximates_planar_front_proved do
    unless allowed.contains ax do
      throwError "The new proof depends on an unexpected axiom: {ax}"
  logInfo "Verified: the proved theorem has exactly the unchanged challenge's type."

assert_no_sorry Planarwave.vHJ_approximates_planar_front_proved
#print axioms Planarwave.vHJ_approximates_planar_front_proved
