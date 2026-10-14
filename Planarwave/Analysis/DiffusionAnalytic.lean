/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.DiffusionSmoothing
import all Planarwave.Analysis.DiffusionSemigroup
import Planarwave.Analysis.SemigroupTaylor
import Planarwave.Analysis.HolomorphicTimeExtension
import Planarwave.Analysis.SemigroupHolomorphic
import Planarwave.Analysis.SemigroupSector

/-!
# Holomorphic time sectors for the principal diffusion semigroup

The diagonal heat bounds imply factorial estimates on all time derivatives. Taylor's
integral remainder identifies the convergent complex power series with the actual real
semigroup on a real interval. The extension disks have radius `η * min t 1`, where the
same `η > 0` works at every positive time and every nonnegative Fourier parameter.

The identity principle glues these disks into a single uniformly bounded holomorphic
extension. Time subdivision continues it to a full sector, where it is strongly
continuous at the vertex, obeys the complex semigroup law, and satisfies a uniform
exponential bound. `SemigroupAnalyticPerturbation` proves preservation of this
analyticity under bounded perturbations. Sectorial resolvent estimates and the
spectral-to-growth implication remain separate obligations in the paper's argument.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {n : ℕ} [Nontrivial (ℝ^n)]

/-- Genuine holomorphic extensions of the principal matrix heat flow, with one radius
factor chosen before the time and Fourier parameter. Their real restrictions are the
already-constructed semigroups. -/
theorem exists_uniform_frontDiffusion_analytic_extension
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c : ℝ) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → ∀ q : ℝ, 0 ≤ q →
      ∃ g : ℂ → (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)),
        AnalyticOnNhd ℂ g (Metric.ball (t : ℂ) (η * min t 1)) ∧
        ∀ s : ℝ, |s - t| < η * min t 1 → g s = frontDiffusionC0Semigroup D hD c q s.toNNReal := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_frontDiffusion_generator_opNorm_bound D hD hDinj c
  let S : {q : ℝ // 0 ≤ q} → C0Semigroup ℂ (BUC ℝ (ℂ^n)) :=
    fun q ↦ frontDiffusionC0Semigroup D hD c q.val
  have hs : ∀ q, ∀ r : NNReal, 0 < r → r ≤ 1 → ∃ B : BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n),
      (∀ v, (S q).HasGeneratorAt (S q r v) (B v)) ∧ ‖B‖ ≤ C / (r : ℝ) := by
    intro q r hr hr₁
    exact hbound q.val q.property r hr hr₁
  obtain ⟨η, hη, hη₁, hg⟩ := C0Semigroup.exists_uniform_analytic_extension_of_smoothing S hC.le hs
  exact ⟨η, hη, hη₁, fun t ht q hq ↦ hg t ht ⟨q, hq⟩⟩

/-- The principal diffusion family has uniformly bounded holomorphic time extensions,
strongly converging to the identity at zero and satisfying the local complex semigroup
law. Both the opening and the bound are chosen before the Fourier parameter. -/
theorem exists_uniform_frontDiffusion_bounded_holomorphic_timeExtension
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c : ℝ) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ N > 0, ∀ q : ℝ, 0 ≤ q →
      ∃ g : ℂ → (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)),
        AnalyticOnNhd ℂ g (positiveTimeNeighborhood η) ∧
        (∀ t : ℝ, 0 < t → g t = frontDiffusionC0Semigroup D hD c q t.toNNReal) ∧
        (∀ z ∈ positiveTimeNeighborhood η, ‖g z‖ ≤ N) ∧
        (∀ v, Tendsto (fun z ↦ g z v) (𝓝[positiveTimeNeighborhood η] 0) (𝓝 v)) ∧
        (∀ z w : ℂ, 0 < z.re → 0 < w.re → |z.im| < η * z.re →
          |w.im| < η * w.re → z.re + w.re ≤ 1 → g (z + w) = (g z).comp (g w)) := by
  obtain ⟨C, hC, hsmooth⟩ := exists_uniform_frontDiffusion_generator_opNorm_bound D hD hDinj c
  obtain ⟨M, hM, μ, hμ, hb⟩ := exists_uniform_frontDiffusion_bound D hD hDinj
  let S : {q : ℝ // 0 ≤ q} → C0Semigroup ℂ (BUC ℝ (ℂ^n)) :=
    fun q ↦ frontDiffusionC0Semigroup D hD c q.val
  have hbound (q : {q : ℝ // 0 ≤ q}) (s : NNReal) : ‖S q s‖ ≤ M := by
    have hexp : Real.exp (-μ * q.val * (s : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hnonneg : 0 ≤ μ * q.val * (s : ℝ) := mul_nonneg (mul_nonneg hμ.le q.property) s.2
      nlinarith
    exact (hb c q.val q.property s).trans
      ((mul_le_mul_of_nonneg_left hexp hM.le).trans_eq (mul_one M))
  obtain ⟨η, hη, hηhalf, L, hL, hext⟩ :=
    C0Semigroup.exists_uniform_bounded_analytic_extension_of_smoothing S hC.le
      (fun q r hr hr₁ ↦ hsmooth q.val q.property r hr hr₁)
  have hη₁ : η ≤ 1 := hηhalf.trans (by norm_num)
  refine ⟨η, hη, hηhalf, L * M, mul_pos hL hM, fun q hq ↦ ?_⟩
  obtain ⟨g, hg, heq, hgb⟩ := exists_bounded_analytic_extension_positiveTimeNeighborhood
    hη hη₁ (fun t ht ↦ hext t ht ⟨q, hq⟩ M hM.le (fun s _ ↦ hbound ⟨q, hq⟩ s))
  refine ⟨g, hg, heq, hgb, ?_, ?_⟩
  · exact fun v ↦ (S ⟨q, hq⟩).tendsto_holomorphicExtension_zero
      hη hη₁ (mul_pos hL hM).le hg heq hgb v
  · exact fun z w hz hw hzi hwi hzw ↦ (S ⟨q, hq⟩).holomorphicExtension_add_small
      hη hη₁ hg heq hz hw hzi hwi hzw

/-- Analytic generation for the actual principal longitudinal diffusion operators:
one full complex time sector and one exponential bound work for every `q ≥ 0`.
The extension agrees with the constructed real semigroup, satisfies the full
semigroup law, and converges strongly to the identity at the sector vertex. -/
theorem exists_uniform_frontDiffusion_holomorphic_sector
    (D : ℝ^n →L[ℝ] ℝ^n) (hD : D.IsPositive) (hDinj : Function.Injective D) (c : ℝ) :
    ∃ η > 0, η ≤ 1 / 2 ∧ ∃ M > 0, ∃ ω > 0, ∀ q : ℝ, 0 ≤ q →
      ∃ G : ℂ → (BUC ℝ (ℂ^n) →L[ℂ] BUC ℝ (ℂ^n)),
        AnalyticOnNhd ℂ G (complexTimeSector η) ∧
        (∀ t : ℝ, 0 < t → G t = frontDiffusionC0Semigroup D hD c q t.toNNReal) ∧
        (∀ z ∈ complexTimeSector η, ∀ w ∈ complexTimeSector η,
          G (z + w) = (G z).comp (G w)) ∧
        (∀ v, Tendsto (fun z ↦ G z v) (𝓝[complexTimeSector η] 0) (𝓝 v)) ∧
        (∀ z ∈ complexTimeSector η, ‖G z‖ ≤ M * Real.exp (ω * z.re)) := by
  obtain ⟨η, hη, hηhalf, N, hN, hext⟩ :=
    exists_uniform_frontDiffusion_bounded_holomorphic_timeExtension D hD hDinj c
  refine ⟨η, hη, hηhalf, Real.exp N, Real.exp_pos N, N, hN, fun q hq ↦ ?_⟩
  obtain ⟨g, hg, hreal, hb, hzero, _⟩ := hext q hq
  let S := frontDiffusionC0Semigroup D hD c q
  obtain ⟨G, hG, hGreal, heq, hdivide⟩ := S.exists_holomorphic_sector_extension hη hg hreal
  exact ⟨G, hG, hGreal,
    fun _ hz _ hw ↦ S.holomorphicSectorExtension_add hη hG hGreal hz hw,
    fun v ↦ C0Semigroup.tendsto_holomorphicSectorExtension_zero heq hzero v,
    fun _ hz ↦ C0Semigroup.norm_holomorphicSectorExtension_le hN.le hb hdivide hz⟩

end

end Planarwave
