/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
module

import all Planarwave.Definitions

/-!
# Longitudinal and transverse coordinates

Elementary facts about the coordinate maps used in `vHJ_approximates_planar_front`.
The solution-side statement definitions are imported without the challenge's admitted theorem.
-/

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

namespace Planarwave

/-- Assembling transverse coordinates with a longitudinal coordinate and projecting back to the
longitudinal coordinate returns the latter. -/
@[simp]
theorem horizontal_full {d : ℕ} (hd : 2 ≤ d) (y : ℝ^(d - 1)) (z : ℝ) :
    horizontal (full y z) = z := by
  simp [horizontal, full, show 1 ≤ d by omega]

/-- Assembling transverse coordinates with a longitudinal coordinate and projecting back to the
transverse coordinates returns the former. -/
@[simp]
theorem transverse_full {d : ℕ} (_hd : 2 ≤ d) (y : ℝ^(d - 1)) (z : ℝ) :
    transverse (full y z) = y := by
  ext i
  simp [transverse, full]

/-- Splitting a point into transverse and longitudinal coordinates and reassembling it returns the
original point. -/
@[simp]
theorem full_transverse_horizontal {d : ℕ} (hd : 2 ≤ d) (x : ℝ^d) :
    full (transverse x) (horizontal x) = x := by
  ext i
  by_cases hi : (i : ℕ) < d - 1
  · simp [full, transverse, hi]
  · have hi_eq : (i : ℕ) = d - 1 := by omega
    have hi_fin : (⟨d - 1, by omega⟩ : Fin d) = i := by
      apply Fin.ext
      exact hi_eq.symm
    simp [full, horizontal, hi_eq, show 1 ≤ d by omega, hi_fin]

/-- Projection onto the longitudinal coordinate is continuous. -/
theorem continuous_horizontal {d : ℕ} (hd : 2 ≤ d) : Continuous (@horizontal d) := by
  unfold horizontal
  simp [show 1 ≤ d by omega]
  fun_prop

/-- Projection onto the transverse coordinates is continuous. -/
theorem continuous_transverse {d : ℕ} : Continuous (@transverse d) := by
  unfold transverse
  fun_prop

/-- Assembly of transverse and longitudinal coordinates is continuous. -/
theorem continuous_full {d : ℕ} :
    Continuous (fun p : ℝ^(d - 1) × ℝ => full p.1 p.2) := by
  unfold full
  refine (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin d => ℝ)).comp ?_
  apply continuous_pi
  intro i
  split_ifs
  · fun_prop
  · fun_prop

/-- The longitudinal/transverse splitting is a linear homeomorphism. -/
noncomputable def coordinateEquiv {d : ℕ} (hd : 2 ≤ d) :
    ℝ^d ≃L[ℝ] (ℝ^(d - 1) × ℝ) where
  toFun x := (transverse x, horizontal x)
  invFun p := full p.1 p.2
  left_inv := full_transverse_horizontal hd
  right_inv p :=
    Prod.ext (transverse_full hd p.1 p.2) (horizontal_full hd p.1 p.2)
  map_add' x x' := by
    ext i
    · simp [transverse]
    · simp [horizontal, show 1 ≤ d by omega]
  map_smul' r x := by
    ext i
    · simp [transverse]
    · simp [horizontal, show 1 ≤ d by omega]
  continuous_toFun := continuous_transverse.prodMk (continuous_horizontal hd)
  continuous_invFun := continuous_full

@[simp]
theorem coordinateEquiv_apply {d : ℕ} (hd : 2 ≤ d) (x : ℝ^d) :
    coordinateEquiv hd x = (transverse x, horizontal x) := rfl

@[simp]
theorem coordinateEquiv_symm_apply {d : ℕ} (hd : 2 ≤ d) (p : ℝ^(d - 1) × ℝ) :
    (coordinateEquiv hd).symm p = full p.1 p.2 := rfl

/-! ## The initial closeness condition -/

/-- The global closeness condition can be checked on the assembled transverse/longitudinal
coordinates.  This is the form used when the initial phase is defined by integrating along each
longitudinal slice. -/
theorem isCloseToFront_iff_full_coordinates
    {d n : ℕ} (hd : 2 ≤ d) (φ : ℝ → ℝ^n) (u : ℝ^d → ℝ^n) (ε : ℝ) :
    IsCloseToFront φ u ε ↔
      ∀ y : ℝ^(d - 1), ∀ z : ℝ, ‖u (full y z) - φ z‖ ≤ ε := by
  constructor
  · intro h y z
    simpa [horizontal_full hd] using h (full y z)
  · intro h x
    simpa [full_transverse_horizontal hd] using h (transverse x) (horizontal x)

end Planarwave
