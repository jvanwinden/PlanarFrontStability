/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupIntertwining
public import Planarwave.Analysis.SemigroupEigenvector
public import Planarwave.Analysis.SemigroupRotation
public import Planarwave.Analysis.SemigroupPerturbationGenerator

@[expose] public section

/-!
# Extending complementary evolution to a fixed ambient space

For compact-family uniformization, the spectral complements vary with the parameter.
We extend each complementary evolution by a prescribed exponential on the critical
eigenline. Its generator differs from the original one by `(ρ-ζ) P`, a bounded
operator. This realizes the appendix's bounded-perturbation argument on one fixed
Banach space, without changing the complementary evolution or its decay rate.
-/

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Changing only the eigenvalue on a commuting spectral projection leaves complementary
evolution exactly unchanged. -/
theorem boundedPerturbation_spectral_comp_complement (S : C0Semigroup ℂ E)
    (P : E →L[ℂ] E) (hP : ∀ x, P (P x) = P x)
    (hcomm : ∀ t : NNReal, (S t).comp P = P.comp (S t)) (b : ℂ) (t : NNReal) :
    (S.boundedPerturbation (b • P) t).comp (ContinuousLinearMap.id ℂ E - P) =
      (S t).comp (ContinuousLinearMap.id ℂ E - P) := by
  let Q := ContinuousLinearMap.id ℂ E - P
  have hQcomm (s : NNReal) : (S s).comp Q = Q.comp (S s) := by
    simp only [Q, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, hcomm]
  have hinter : (S.boundedPerturbation (b • P) t).comp Q = Q.comp (S t) := by
    apply S.comp_eq_comp_of_generator_intertwining
    intro x y hxy
    rw [S.boundedPerturbation_hasGeneratorAt_iff]
    have hzero : (b • P) (Q x) = 0 := by
      change b • P (x - P x) = 0
      rw [map_sub, hP, sub_self, smul_zero]
    rw [hzero, sub_zero]
    exact hxy.map_of_comp_comm Q hQcomm
  exact hinter.trans (hQcomm t).symm

/-- Exact spectral splitting for the extension with critical exponential `exp(t ρ)`. -/
theorem boundedPerturbation_spectral_eq (S : C0Semigroup ℂ E)
    (P : E →L[ℂ] E) {ζ : ℂ} (hP : ∀ x, P (P x) = P x)
    (hcomm : ∀ t : NNReal, (S t).comp P = P.comp (S t))
    (heig : ∀ x, S.HasGeneratorAt (P x) (ζ • P x)) (ρ : ℂ) (t : NNReal) :
    S.boundedPerturbation ((ρ - ζ) • P) t =
      (S t).comp (ContinuousLinearMap.id ℂ E - P) + Complex.exp ((t : ℂ) * ρ) • P := by
  let T := S.boundedPerturbation ((ρ - ζ) • P)
  have heigT : ∀ x, T.HasGeneratorAt (P x) (ρ • P x) := by
    intro x
    rw [boundedPerturbation_hasGeneratorAt_iff]
    have h : ρ • P x - ((ρ - ζ) • P) (P x) = ζ • P x := by
      change ρ • P x - (ρ - ζ) • P (P x) = ζ • P x
      rw [hP, sub_smul]
      abel
    rw [h]
    exact heig x
  have hcritical := T.comp_eq_exp_smul_of_generator_eigenrange P ρ heigT t
  have hcomp := S.boundedPerturbation_spectral_comp_complement P hP hcomm (ρ - ζ) t
  calc
    T t = (T t).comp (ContinuousLinearMap.id ℂ E - P) + (T t).comp P := by
      simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, sub_add_cancel]
    _ = _ := by rw [hcomp, hcritical]

/-- A complementary bound extends to the ambient space by choosing a critical exponential
with no greater growth rate. This supplies the individual bounds for the appendix lemma. -/
theorem norm_boundedPerturbation_spectral_le (S : C0Semigroup ℂ E)
    (P : E →L[ℂ] E) {ζ : ℂ} (hP : ∀ x, P (P x) = P x)
    (hcomm : ∀ t : NNReal, (S t).comp P = P.comp (S t))
    (heig : ∀ x, S.HasGeneratorAt (P x) (ζ • P x)) {ρ ω M : ℝ}
    (hρ : ρ ≤ ω)
    (hb : ∀ t : NNReal, ‖(S t).comp (ContinuousLinearMap.id ℂ E - P)‖ ≤
      M * Real.exp (ω * t)) (t : NNReal) :
    ‖S.boundedPerturbation (((ρ : ℂ) - ζ) • P) t‖ ≤
      (M + ‖P‖) * Real.exp (ω * t) := by
  rw [S.boundedPerturbation_spectral_eq P hP hcomm heig]
  have hexp : ‖Complex.exp ((t : ℂ) * (ρ : ℂ))‖ ≤ Real.exp (ω * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hρ t.2
  calc
    ‖(S t).comp (ContinuousLinearMap.id ℂ E - P) + Complex.exp ((t : ℂ) * ρ) • P‖ ≤
        ‖(S t).comp (ContinuousLinearMap.id ℂ E - P)‖ +
          ‖Complex.exp ((t : ℂ) * ρ) • P‖ := norm_add_le _ _
    _ ≤ M * Real.exp (ω * t) + Real.exp (ω * t) * ‖P‖ :=
      add_le_add (hb t) (by rw [norm_smul]; exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
    _ = _ := by ring

end

end C0Semigroup
