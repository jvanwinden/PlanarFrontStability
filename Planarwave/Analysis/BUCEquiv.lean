/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI Codex
-/
module

public import Planarwave.Analysis.BUC
public import Mathlib.Topology.Algebra.Module.Equiv

@[expose] public section

/-!
# Continuous linear equivalences on BUC spaces

A continuous linear change of coordinates in the target induces the corresponding pointwise
change of coordinates on bounded uniformly continuous functions.  This is the function-space
version of the eigenvector matrix used in the proof of Lemma 2.2.
-/

namespace BUC

noncomputable section

variable {α 𝕜 E F : Type*} [UniformSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise postcomposition by a continuous linear equivalence. -/
def postcompCLE (e : E ≃L[𝕜] F) : BUC α E ≃L[𝕜] BUC α F :=
  ContinuousLinearEquiv.equivOfInverse
    (postcompCLM e.toContinuousLinearMap)
    (postcompCLM e.symm.toContinuousLinearMap)
    (fun f ↦ by ext x; simp)
    (fun f ↦ by ext x; simp)

@[simp]
theorem postcompCLE_apply (e : E ≃L[𝕜] F) (f : BUC α E) (x : α) :
    postcompCLE e f x = e (f x) := rfl

@[simp]
theorem postcompCLE_symm_apply (e : E ≃L[𝕜] F) (f : BUC α F) (x : α) :
    (postcompCLE e).symm f x = e.symm (f x) := rfl

section Pi

variable {ι : Type*} [Fintype ι]
  {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]

/-- Assemble a finite family of `BUC` functions into a `BUC` function with values in the
corresponding product. -/
def ofPi (f : ∀ i, BUC α (X i)) : BUC α (∀ i, X i) where
  toBCF := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x i ↦ f i x)
    (continuous_pi fun i ↦ (f i).continuous)
    ‖f‖
    (fun x ↦ by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
      intro i
      exact (f i).norm_apply_le x |>.trans (norm_le_pi_norm f i))
  uniformContinuous' := uniformContinuous_pi.mpr fun i ↦ (f i).uniformContinuous

@[simp]
theorem ofPi_apply (f : ∀ i, BUC α (X i)) (x : α) (i : ι) :
    ofPi f x i = f i x := rfl

/-- Assembly of a finite family of `BUC` functions is continuous linear. -/
def ofPiCLM : (∀ i, BUC α (X i)) →L[𝕜] BUC α (∀ i, X i) :=
  LinearMap.mkContinuous
    { toFun := ofPi
      map_add' := fun f g ↦ by ext x i; rfl
      map_smul' := fun c f ↦ by ext x i; rfl }
    1 fun f ↦ by
      rw [one_mul]
      apply (BUC.norm_le (norm_nonneg f)).2
      intro x
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
      intro i
      exact (f i).norm_apply_le x |>.trans (norm_le_pi_norm f i)

@[simp]
theorem ofPiCLM_apply (f : ∀ i, BUC α (X i)) (x : α) (i : ι) :
    ofPiCLM (𝕜 := 𝕜) f x i = f i x := rfl

/-- Read a product-valued `BUC` function coordinatewise. -/
def toPiCLM : BUC α (∀ i, X i) →L[𝕜] (∀ i, BUC α (X i)) :=
  ContinuousLinearMap.pi fun i ↦
    postcompCLM (ContinuousLinearMap.proj i : (∀ i, X i) →L[𝕜] X i)

@[simp]
theorem toPiCLM_apply (f : BUC α (∀ i, X i)) (i : ι) (x : α) :
    toPiCLM (𝕜 := 𝕜) f i x = f x i := rfl

/-- The coordinate-reading map does not increase the supremum norm. -/
theorem norm_toPiCLM_apply_le (f : BUC α (∀ i, X i)) :
    ‖toPiCLM (𝕜 := 𝕜) f‖ ≤ ‖f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
  intro i
  apply (BUC.norm_le (norm_nonneg f)).2
  intro x
  exact (norm_le_pi_norm (f x) i).trans (f.norm_apply_le x)

/-- Finite products commute with the `BUC` construction, as a continuous linear equivalence. -/
def piCLE : BUC α (∀ i, X i) ≃L[𝕜] (∀ i, BUC α (X i)) :=
  ContinuousLinearEquiv.equivOfInverse
    toPiCLM ofPiCLM
    (fun f ↦ by ext i x; rfl)
    (fun f ↦ by ext x i; rfl)

@[simp]
theorem piCLE_apply (f : BUC α (∀ i, X i)) (i : ι) (x : α) :
    piCLE (𝕜 := 𝕜) f i x = f x i := rfl

@[simp]
theorem piCLE_symm_apply (f : ∀ i, BUC α (X i)) (x : α) (i : ι) :
    (piCLE (α := α) (𝕜 := 𝕜) (X := X)).symm f x i = f i x := rfl

end Pi

end

end BUC
