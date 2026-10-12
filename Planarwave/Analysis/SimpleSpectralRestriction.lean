/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SimpleSpectralProjection

@[expose] public section

/-!
# The kernel at the perturbed simple eigenvalue

The invertible Fredholm block shows that every critical kernel vector is a multiple
of the constructed eigenvector. Thus the critical projection is the identity on
that kernel, as required when removing the eigenvalue on the complementary space.
-/

open Filter Topology

namespace Planarwave.SimpleFredholmZeroMode

noncomputable section

variable {X Dom : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Dom] [NormedSpace ℂ Dom] [CompleteSpace Dom]

variable (S : SimpleFredholmZeroMode X Dom)

/-- All vectors in the critical kernel lie on the perturbed eigenline. -/
theorem eq_smul_eigenvectorBranch_of_criticalPencil_eq_zero
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible)
    (heig : S.criticalPencil B q (S.eigenvectorBranch B q) = 0)
    (v : Dom) (hv : S.criticalPencil B q v = 0) :
    v = S.functional (S.inclusion v) • S.eigenvectorBranch B q := by
  have h := S.criticalComplementSolution_criticalPencil B q hC heig v
  rw [hv, map_zero, eq_comm, sub_eq_zero] at h
  conv_lhs => rw [S.domain_eq_neutral_add_complement v, h]
  simp only [eigenvectorBranch, Submodule.coe_smul, smul_add]

/-- The normalized spectral projection fixes every embedded critical kernel vector. -/
theorem criticalProjection_inclusion_of_criticalPencil_eq_zero
    (B : Dom →L[ℂ] X) (q : ℂ)
    (hC : (S.criticalComplementPencil B q).IsInvertible)
    (heig : S.criticalPencil B q (S.eigenvectorBranch B q) = 0)
    (hn : S.criticalNormalization B q ≠ 0)
    (v : Dom) (hv : S.criticalPencil B q v = 0) :
    S.criticalProjection B q (S.inclusion v) = S.inclusion v := by
  have h := S.eq_smul_eigenvectorBranch_of_criticalPencil_eq_zero B q hC heig v hv
  conv_lhs => rw [h]
  rw [map_smul, map_smul, S.criticalProjection_apply,
    S.criticalLeftFunctional_eigenvector B q hn, one_smul, ← map_smul, ← h]

/-- The critical projection fixes the full critical kernel for every sufficiently small
perturbation parameter, not just the explicitly constructed eigenvector. -/
theorem eventually_criticalProjection_fixes_kernel (B : Dom →L[ℂ] X) :
    ∀ᶠ q in 𝓝 0, ∀ v, S.criticalPencil B q v = 0 →
      S.criticalProjection B q (S.inclusion v) = S.inclusion v := by
  filter_upwards [S.eventually_criticalComplementPencil_isInvertible B,
    S.eventually_criticalPencil_eigenvector_eq_zero B,
    S.eventually_criticalNormalization_ne_zero B] with q hC heig hn
  exact S.criticalProjection_inclusion_of_criticalPencil_eq_zero B q hC heig hn

end

end Planarwave.SimpleFredholmZeroMode
