/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HolomorphicTimeExtension

@[expose] public section

/-! # Geometry and uniqueness for complex time sectors -/

open Filter Set Topology

namespace Planarwave

noncomputable section

/-- An open sector about the positive real axis, described without choosing arguments. -/
def complexTimeSector (η : ℝ) : Set ℂ := {z | 0 < z.re ∧ |z.im| < η * z.re}

theorem isOpen_complexTimeSector (η : ℝ) : IsOpen (complexTimeSector η) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im.abs (continuous_const.mul Complex.continuous_re))

theorem convex_complexTimeSector (η : ℝ) : Convex ℝ (complexTimeSector η) := by
  have h₁ : Convex ℝ {z : ℂ | 0 < z.re} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have h₂ : Convex ℝ {z : ℂ | 0 < η * z.re - z.im} := (convex_Ioi (0 : ℝ)).linear_preimage
    (η • Complex.reCLM.toLinearMap - Complex.imCLM.toLinearMap)
  have h₃ : Convex ℝ {z : ℂ | 0 < η * z.re + z.im} := (convex_Ioi (0 : ℝ)).linear_preimage
    (η • Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap)
  convert h₁.inter (h₂.inter h₃) using 1
  apply Set.ext
  intro z
  change (0 < z.re ∧ |z.im| < η * z.re) ↔
    (0 < z.re ∧ 0 < η * z.re - z.im ∧ 0 < η * z.re + z.im)
  rw [abs_lt]
  constructor <;> intro h <;> constructor
  · exact h.1
  · constructor <;> linarith [h.2.1, h.2.2]
  · exact h.1
  · constructor <;> linarith [h.2.1, h.2.2]

theorem mem_complexTimeSector_real {η t : ℝ} (hη : 0 < η) (ht : 0 < t) :
    (t : ℂ) ∈ complexTimeSector η := by
  exact ⟨ht, by simpa only [Complex.ofReal_im, abs_zero, Complex.ofReal_re] using mul_pos hη ht⟩

theorem add_mem_complexTimeSector {η : ℝ} {z w : ℂ}
    (hz : z ∈ complexTimeSector η) (hw : w ∈ complexTimeSector η) :
    z + w ∈ complexTimeSector η := by
  refine ⟨add_pos hz.1 hw.1, ?_⟩
  calc
    |(z + w).im| ≤ |z.im| + |w.im| := abs_add_le _ _
    _ < η * z.re + η * w.re := add_lt_add hz.2 hw.2
    _ = η * (z + w).re := by rw [Complex.add_re]; ring

theorem div_real_mem_complexTimeSector {η r : ℝ} {z : ℂ}
    (hz : z ∈ complexTimeSector η) (hr : 0 < r) :
    z / (r : ℂ) ∈ complexTimeSector η := by
  simp only [complexTimeSector, mem_ofPred_eq, Complex.div_ofReal_re, Complex.div_ofReal_im]
  refine ⟨div_pos hz.1 hr, ?_⟩
  rw [abs_div, abs_of_pos hr, ← mul_div_assoc]
  exact div_lt_div_of_pos_right hz.2 hr

theorem real_mul_mem_complexTimeSector {η r : ℝ} {z : ℂ}
    (hz : z ∈ complexTimeSector η) (hr : 0 < r) :
    (r : ℂ) * z ∈ complexTimeSector η := by
  simp only [complexTimeSector, mem_ofPred_eq, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  refine ⟨mul_pos hr hz.1, ?_⟩
  rw [abs_mul, abs_of_pos hr]
  nlinarith [mul_lt_mul_of_pos_left hz.2 hr]

theorem mem_positiveTimeNeighborhood_of_sector {η : ℝ} {z : ℂ}
    (hz : z ∈ complexTimeSector η) (hz₁ : z.re ≤ 1) :
    z ∈ positiveTimeNeighborhood η :=
  mem_positiveTimeNeighborhood_of_im_lt hz.1 (by simpa only [min_eq_left hz₁] using hz.2)

/-- On an open preconnected set meeting the real axis, real agreement determines a
holomorphic function. This is used to compare the time-subdivision extensions. -/
theorem eqOn_of_analytic_of_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : ℂ → F} {U : Set ℂ} {a : ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (ha : (a : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → f t = g t) : EqOn f g U := by
  have htend : Tendsto Complex.ofReal (𝓝[≠] a) (𝓝[≠] (a : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Complex.ofReal_injective.ne ht
  have hevent : ∀ᶠ t : ℝ in 𝓝 a, f (t : ℂ) = g (t : ℂ) := by
    filter_upwards [Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds ha)] with t ht
    exact hreal t ht
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn ha
    (htend.frequently (hevent.filter_mono nhdsWithin_le_nhds).frequently)

end

end Planarwave
