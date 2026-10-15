/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Definitions
import Planarwave.Analysis.BUC

/-!
# Bridges from the challenge predicates to bundled analytic spaces

The theorem statement deliberately uses the unbundled predicate `IsBUC`.  The paper's linear and
nonlinear arguments need the corresponding Banach space, so this file proves the exact conversion
in both directions.
-/

open Set

namespace Planarwave

noncomputable section

variable {A E : Type*} [UniformSpace A] [NormedAddCommGroup E]

/-- A bundled BUC function satisfies the unbundled predicate used in `Challenge.lean`. -/
theorem isBUC_coe (g : BUC A E) : IsBUC (g : A → E) := by
  constructor
  · simpa [uniformContinuousOn_univ] using g.uniformContinuous
  · exact ⟨‖g‖, fun x _ ↦ g.norm_apply_le x⟩

/-- Every function satisfying the challenge's `IsBUC` predicate has a canonical representative in
the bundled Banach space `BUC`. -/
def BUC.ofIsBUC {g : A → E} (hg : IsBUC g) : BUC A E where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup g
    (uniformContinuousOn_univ.mp hg.1).continuous hg.2.choose
    (fun x ↦ hg.2.choose_spec x (mem_univ x))
  uniformContinuous' := uniformContinuousOn_univ.mp hg.1

@[simp]
theorem BUC.ofIsBUC_apply {g : A → E} (hg : IsBUC g) (x : A) :
    BUC.ofIsBUC hg x = g x := rfl

end

end Planarwave
