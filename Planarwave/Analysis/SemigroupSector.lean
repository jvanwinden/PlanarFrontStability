/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupHolomorphic
public import Planarwave.Analysis.ComplexTimeSector
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

/-!
# Extending a holomorphic semigroup to a full time sector

Time subdivision gives local extensions on increasingly long truncated sectors.
Their real restrictions are the original semigroup, so the identity principle makes
them agree on overlaps. This supplies the full-sector continuation needed in the
analytic-semigroup part of the paper's Section 2.
-/

open Filter Set Topology Planarwave

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem pow_eq_nsmul_time (S : C0Semigroup ℂ E) (t : NNReal) (n : ℕ) :
    (S t) ^ n = S (n • t) := by
  induction n with
  | zero => simp only [pow_zero, zero_nsmul, S.map_zero]; rfl
  | succ n ih => rw [pow_succ, succ_nsmul, S.map_add, ih]; rfl

/-- Continuation by finite time subdivision. The last clause records the subdivision
formula for every admissible positive integer, not just the one chosen by gluing. -/
theorem exists_holomorphic_sector_extension (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) {g : ℂ → (E →L[ℂ] E)}
    (hg : AnalyticOnNhd ℂ g (positiveTimeNeighborhood η))
    (hreal : ∀ t : ℝ, 0 < t → g t = S t.toNNReal) :
    ∃ G : ℂ → (E →L[ℂ] E), AnalyticOnNhd ℂ G (complexTimeSector η) ∧
      (∀ t : ℝ, 0 < t → G t = S t.toNNReal) ∧
      EqOn G g (complexTimeSector η ∩ {z | z.re < 1}) ∧
      (∀ z ∈ complexTimeSector η, ∀ n : ℕ, 0 < n → z.re < n →
        G z = (g (z / (n : ℂ))) ^ n) := by
  classical
  let U (n : {n : ℕ // 0 < n}) : Set ℂ := complexTimeSector η ∩ {z | z.re < n.val}
  let H (n : {n : ℕ // 0 < n}) (z : ℂ) : E →L[ℂ] E := (g (z / (n.val : ℂ))) ^ n.val
  have hopen (n) : IsOpen (U n) := (isOpen_complexTimeSector η).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hconv (n) : Convex ℝ (U n) := (convex_complexTimeSector η).inter
    ((convex_Iio (n.val : ℝ)).linear_preimage Complex.reCLM.toLinearMap)
  have hanalytic (n) : AnalyticOnNhd ℂ (H n) (U n) := by
    intro z hz
    have hn : 0 < (n.val : ℝ) := by exact_mod_cast n.property
    have hzdiv : z / (n.val : ℂ) ∈ positiveTimeNeighborhood η := by
      apply mem_positiveTimeNeighborhood_of_sector
        (by simpa only [Complex.ofReal_natCast] using div_real_mem_complexTimeSector hz.1 hn)
      rw [← Complex.ofReal_natCast, Complex.div_ofReal_re]
      exact ((div_lt_one hn).mpr hz.2).le
    exact ((hg _ hzdiv).comp (f := fun z : ℂ ↦ z / (n.val : ℂ))
      analyticAt_id.div_const).pow n.val
  have hrealH (n : {n : ℕ // 0 < n}) (t : ℝ) (ht : 0 < t) : H n t = S t.toNNReal := by
    have hn : 0 < (n.val : ℝ) := by exact_mod_cast n.property
    have hco : (t : ℂ) / (n.val : ℂ) = ((t / (n.val : ℝ) : ℝ) : ℂ) := by simp
    have htime : n.val • (t / (n.val : ℝ)).toNNReal = t.toNNReal := by
      apply NNReal.eq
      simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
        Real.coe_toNNReal _ (div_pos ht hn).le, Real.coe_toNNReal _ ht.le]
      field_simp
    dsimp only [H]
    rw [hco, hreal _ (div_pos ht hn), S.pow_eq_nsmul_time, htime]
  have hcompat (n m) : EqOn (H n) (H m) (U n ∩ U m) := by
    intro z hz
    have hre : (z.re : ℂ) ∈ U n ∩ U m :=
      ⟨⟨mem_complexTimeSector_real hη hz.1.1.1, hz.1.2⟩,
        ⟨mem_complexTimeSector_real hη hz.2.1.1, hz.2.2⟩⟩
    exact eqOn_of_analytic_of_real ((hopen n).inter (hopen m))
      ((hconv n).inter (hconv m)).isPreconnected hre
      ((hanalytic n).mono inter_subset_left) ((hanalytic m).mono inter_subset_right)
      (fun t ht ↦ (hrealH n t ht.1.1.1).trans (hrealH m t ht.1.1.1).symm) hz
  have hcover {z : ℂ} (hz : z ∈ complexTimeSector η) :
      ∃ n : {n : ℕ // 0 < n}, z ∈ U n := by
    obtain ⟨n, hn⟩ := exists_nat_gt z.re
    have hnpos : 0 < n := by exact_mod_cast (hz.1.trans hn)
    exact ⟨⟨n, hnpos⟩, hz, hn⟩
  let G : ℂ → (E →L[ℂ] E) := fun z ↦ if hz : z ∈ complexTimeSector η then
    H (hcover hz).choose z else 0
  have heq (n) {z : ℂ} (hz : z ∈ U n) : G z = H n z := by
    simp only [G, dif_pos hz.1]
    exact hcompat _ n ⟨(hcover hz.1).choose_spec, hz⟩
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := hcover hz
    apply (hanalytic n z hn).congr
    filter_upwards [(hopen n).mem_nhds hn] with w hw
    exact (heq n hw).symm
  · intro t ht
    obtain ⟨n, hn⟩ := hcover (mem_complexTimeSector_real hη ht)
    exact (heq n hn).trans (hrealH n t ht)
  · intro z hz
    simpa only [H, Nat.cast_one, div_one, pow_one] using
      heq ⟨1, zero_lt_one⟩ (by simpa only [U, Nat.cast_one] using hz)
  · intro z hz n hn hzn
    exact heq ⟨n, hn⟩ ⟨hz, hzn⟩

/-- Real time shifts of a full-sector continuation obey the semigroup law. -/
theorem holomorphicSectorExtension_add_real (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    {z : ℂ} (hz : z ∈ complexTimeSector η) {s : ℝ} (hs : 0 ≤ s) :
    G (z + (s : ℂ)) = (G z).comp (S s.toNNReal) := by
  by_cases hs₀ : s = 0
  · subst s
    simp
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs₀)
  have hshift : AnalyticOnNhd ℂ (fun w ↦ G (w + (s : ℂ))) (complexTimeSector η) := by
    intro w hw
    exact (hG _ (add_mem_complexTimeSector hw (mem_complexTimeSector_real hη hspos))).comp
      (f := fun w ↦ w + (s : ℂ)) (analyticAt_id.add analyticAt_const)
  have hcomp : AnalyticOnNhd ℂ (fun w ↦ (G w).comp (S s.toNNReal)) (complexTimeSector η) := by
    intro w hw
    exact (((ContinuousLinearMap.compL ℂ E E E).flip (S s.toNNReal)).analyticAt (G w)).comp (hG w hw)
  apply eqOn_of_analytic_of_real (isOpen_complexTimeSector η) (convex_complexTimeSector η).isPreconnected
    (mem_complexTimeSector_real hη zero_lt_one) hshift hcomp _ hz
  intro t ht
  have htpos : 0 < t := ht.1
  rw [← Complex.ofReal_add, hreal _ (add_pos htpos hspos), hreal _ htpos,
    Real.toNNReal_add htpos.le hs, S.map_add]

/-- The full complex semigroup law follows by analytic continuation in each time
variable. The sector is stable under addition, so no small-time restriction remains. -/
theorem holomorphicSectorExtension_add (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal)
    {z w : ℂ} (hz : z ∈ complexTimeSector η) (hw : w ∈ complexTimeSector η) :
    G (z + w) = (G z).comp (G w) := by
  have hshift : AnalyticOnNhd ℂ (fun v ↦ G (z + v)) (complexTimeSector η) := by
    intro v hv
    exact (hG _ (add_mem_complexTimeSector hz hv)).comp
      (f := fun v ↦ z + v) (analyticAt_const.add analyticAt_id)
  have hcomp : AnalyticOnNhd ℂ (fun v ↦ (G z).comp (G v)) (complexTimeSector η) := by
    intro v hv
    exact ((ContinuousLinearMap.compL ℂ E E E (G z)).analyticAt (G v)).comp (hG v hv)
  apply eqOn_of_analytic_of_real (isOpen_complexTimeSector η) (convex_complexTimeSector η).isPreconnected
    (mem_complexTimeSector_real hη zero_lt_one) hshift hcomp _ hw
  intro t ht
  have htpos : 0 < t := ht.1
  rw [S.holomorphicSectorExtension_add_real hη hG hreal hz htpos.le, hreal _ htpos]

/-- A bounded operator commuting with the real semigroup also commutes with its
holomorphic sector extension. In particular the critical spectral splitting is
preserved at complex times, as needed when applying analytic decay to its complement. -/
theorem holomorphicSectorExtension_comp_comm (S : C0Semigroup ℂ E)
    {η : ℝ} (hη : 0 < η) {G : ℂ → (E →L[ℂ] E)}
    (hG : AnalyticOnNhd ℂ G (complexTimeSector η))
    (hreal : ∀ t : ℝ, 0 < t → G t = S t.toNNReal) (P : E →L[ℂ] E)
    (hcomm : ∀ t : NNReal, (S t).comp P = P.comp (S t))
    {z : ℂ} (hz : z ∈ complexTimeSector η) : (G z).comp P = P.comp (G z) := by
  have hleft : AnalyticOnNhd ℂ (fun w ↦ (G w).comp P) (complexTimeSector η) := by
    intro w hw
    exact (((ContinuousLinearMap.compL ℂ E E E).flip P).analyticAt (G w)).comp (hG w hw)
  have hright : AnalyticOnNhd ℂ (fun w ↦ P.comp (G w)) (complexTimeSector η) := by
    intro w hw
    exact ((ContinuousLinearMap.compL ℂ E E E P).analyticAt (G w)).comp (hG w hw)
  apply eqOn_of_analytic_of_real (isOpen_complexTimeSector η) (convex_complexTimeSector η).isPreconnected
    (mem_complexTimeSector_real hη zero_lt_one) hleft hright _ hz
  intro t ht
  have htpos : 0 < t := ht.1
  rw [hreal t htpos]
  exact hcomm t.toNNReal

omit [CompleteSpace E] in
/-- A bound on the initial time neighborhood becomes an exponential bound on the
whole sector. The constants depend only on the initial bound, not on time. -/
theorem norm_holomorphicSectorExtension_le {η M : ℝ} (hM : 0 ≤ M)
    {g G : ℂ → (E →L[ℂ] E)}
    (hbound : ∀ z ∈ positiveTimeNeighborhood η, ‖g z‖ ≤ M)
    (hdivide : ∀ z ∈ complexTimeSector η, ∀ n : ℕ, 0 < n → z.re < n →
      G z = (g (z / (n : ℂ))) ^ n)
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    ‖G z‖ ≤ Real.exp M * Real.exp (M * z.re) := by
  let n : ℕ := ⌊z.re⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hzn : z.re < n := by simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one z.re
  have hnle : (n : ℝ) ≤ z.re + 1 := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le hz.1.le]
  have hzdiv : z / (n : ℂ) ∈ positiveTimeNeighborhood η := by
    apply mem_positiveTimeNeighborhood_of_sector
      (by simpa only [Complex.ofReal_natCast] using div_real_mem_complexTimeSector hz hnreal)
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re]
    exact ((div_lt_one hnreal).mpr hzn).le
  rw [hdivide z hz n hn hzn]
  calc
    ‖g (z / (n : ℂ)) ^ n‖ ≤ ‖g (z / (n : ℂ))‖ ^ n := norm_pow_le' _ hn
    _ ≤ M ^ n := pow_le_pow_left₀ (norm_nonneg _) (hbound _ hzdiv) n
    _ ≤ (Real.exp M) ^ n := pow_le_pow_left₀ hM (by linarith [Real.add_one_le_exp M]) n
    _ = Real.exp (M * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (M * (z.re + 1)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnle hM)
    _ = Real.exp M * Real.exp (M * z.re) := by rw [mul_add, Real.exp_add, mul_one, mul_comm]

omit [CompleteSpace E] in
/-- The full-sector continuation inherits strong continuity at the vertex from
its agreement with the bounded local extension. -/
theorem tendsto_holomorphicSectorExtension_zero {η : ℝ}
    {g G : ℂ → (E →L[ℂ] E)}
    (heq : EqOn G g (complexTimeSector η ∩ {z | z.re < 1}))
    (hzero : ∀ x, Tendsto (fun z ↦ g z x) (𝓝[positiveTimeNeighborhood η] 0) (𝓝 x)) (x : E) :
    Tendsto (fun z ↦ G z x) (𝓝[complexTimeSector η] 0) (𝓝 x) := by
  have hsmall : ∀ᶠ z : ℂ in 𝓝[complexTimeSector η] 0, z.re < 1 := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
  have hmap : Tendsto (fun z : ℂ ↦ z) (𝓝[complexTimeSector η] 0)
      (𝓝[positiveTimeNeighborhood η] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hz₁
    exact mem_positiveTimeNeighborhood_of_sector hz hz₁.le
  apply ((hzero x).comp hmap).congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with z hz hz₁
  exact congrArg (fun T : E →L[ℂ] E ↦ T x) (heq ⟨hz, hz₁⟩).symm

end

end C0Semigroup
