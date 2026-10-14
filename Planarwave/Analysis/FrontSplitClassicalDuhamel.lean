/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

import all Planarwave.Analysis.FrontClassicalDuhamel
import all Planarwave.Analysis.RealSpatialEmbeddingRegularity
import all Planarwave.Analysis.CoordinateLaplacian

/-!
# The real split-coordinate equation and the spatial Duhamel response

The modulation equation is written with real states in transverse and
longitudinal coordinates. Its linear part intertwines with the actual full
complex front generator. Consequently the classical modulation equation
gives the semigroup response estimated in the tracking argument.
-/

open Set
open scoped Laplacian

namespace Planarwave

noncomputable section

set_option maxHeartbeats 1200000

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)
local notation "ℂ^" n:arg => EuclideanSpace ℂ (Fin n)

variable {d n : ℕ}

/-- The real spatial embedding transports the split Laplacian to the
Euclidean Laplacian, despite the different norms on the coordinate spaces. -/
theorem laplacian_embedSplitSpatial (hd : 2 ≤ d)
    (v : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) (hv : ContDiff ℝ 2 (v : _ → _))
    (x : ℝ^d) :
    Δ (embedSplitSpatial hd v : ℝ^d → ℂ^n) x =
      embed (splitLaplacian v (transverse x, horizontal x)) := by
  let u : ℝ^d → ℝ^n := fun x ↦ v (coordinateEquiv hd x)
  have hu : ContDiff ℝ 2 u := hv.comp (coordinateEquiv hd).contDiff
  have hlap : Δ u x = splitLaplacian v (transverse x, horizontal x) := by
    simpa only [u, coordinateEquiv_apply, transverse_full hd, horizontal_full hd,
      full_transverse_horizontal hd] using
      laplacian_eq_splitLaplacian hd u hu (transverse x) (horizontal x)
  have h := hu.contDiffAt.laplacian_CLM_comp_left
    (l := (realStateEmbeddingCLM : ℝ^n →L[ℝ] ℂ^n)) (x := x)
  change Δ (embedSplitSpatial hd v : ℝ^d → ℂ^n) x = embed (Δ u x) at h
  rw [h, hlap]

/-- The physical drift corresponds exactly to the longitudinal derivative
in split coordinates. -/
theorem fderiv_embedSplitSpatial_drift (hd : 2 ≤ d) (c : ℝ)
    (v : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) (hv : ContDiff ℝ 2 (v : _ → _))
    (x : ℝ^d) :
    fderiv ℝ (embedSplitSpatial hd v) x (frontSpatialDrift hd c) =
      embed (c • fderiv ℝ v (transverse x, horizontal x) (0, 1)) := by
  have h := (realStateEmbeddingCLM : ℝ^n →L[ℝ] ℂ^n).hasFDerivAt.comp x
    (((hv.differentiable (by norm_num) (coordinateEquiv hd x)).hasFDerivAt).comp x
      (coordinateEquiv hd).hasFDerivAt)
  have heq := congrArg (fun L : ℝ^d →L[ℝ] ℂ^n ↦ L (frontSpatialDrift hd c)) h.fderiv
  change fderiv ℝ (embedSplitSpatial hd v) x (frontSpatialDrift hd c) =
    embed (fderiv ℝ v (coordinateEquiv hd x)
      (coordinateEquiv hd (frontSpatialDrift hd c))) at heq
  rw [heq, frontSpatialDrift_coordinates]
  have hc : ((0, c) : ℝ^(d - 1) × ℝ) = c • (0, 1) := by simp
  rw [hc, map_smul]
  rfl

variable (f : ℝ^n → ℝ^n) (D : ℝ^n →L[ℝ] ℝ^n) (c : ℝ)
  (φ : ℝ → ℝ^n) (h₁ : IsSmoothParabolic f D) (h₂ : IsSmoothFront f D c φ)
  (hd : 2 ≤ d) [Nontrivial (ℝ^n)]

omit [Nontrivial (ℝ^n)] in
/-- The real split-coordinate linear expression is the restriction of the
full complex front generator to real data. -/
theorem frontSpatial_expression_embedSplitSpatial
    (v : BUC (ℝ^(d - 1) × ℝ) (ℝ^n)) (hv : ContDiff ℝ 2 (v : _ → _))
    (x : ℝ^d) :
    frontComplexifiedDiffusion D (Δ (embedSplitSpatial hd v : ℝ^d → ℂ^n) x) +
      fderiv ℝ (embedSplitSpatial hd v) x (frontSpatialDrift hd c) +
      (fderiv ℝ f (φ (horizontal x))).complexify (embedSplitSpatial hd v x) =
    embed (D (splitLaplacian v (transverse x, horizontal x)) +
      c • fderiv ℝ v (transverse x, horizontal x) (0, 1) +
      fderiv ℝ f (φ (horizontal x)) (v (transverse x, horizontal x))) := by
  rw [laplacian_embedSplitSpatial hd v hv, fderiv_embedSplitSpatial_drift hd c v hv,
    frontComplexifiedDiffusion_apply, embedSplitSpatial_apply]
  simp only [← challengeComplexifyCLM_apply, challengeComplexifyCLM_embed]
  change realStateEmbeddingCLM _ + realStateEmbeddingCLM _ + realStateEmbeddingCLM _ =
    realStateEmbeddingCLM (_ + _ + _)
  simp only [map_add]

/-- The classical real modulation equation gives exactly the spatial
Duhamel response. Only positive-time spatial derivatives are required;
the initial perturbation and source are merely continuous BUC paths. -/
theorem embedSplitSpatial_eq_realOrbit_add_duhamel_of_classical
    {T : ℝ} {v F : ℝ → BUC (ℝ^(d - 1) × ℝ) (ℝ^n)}
    (hv : ContinuousOn v (Icc 0 T)) (hF : ContinuousOn F (Icc 0 T))
    (hreg : BUCSpatialRegularOn (Ioo 0 T) 2 v)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ y z, HasDerivAt (fun r ↦ v r (y, z))
      (D (splitLaplacian (v t) (y, z)) +
        c • fderiv ℝ (v t) (y, z) (0, 1) +
        fderiv ℝ f (φ z) (v t (y, z)) + F t (y, z)) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    embedSplitSpatial hd (v t) =
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).realOrbit
        (embedSplitSpatial hd (v 0)) t +
      (frontSpatialC0Semigroup f D c φ h₁ h₂ hd).duhamel
        (fun r ↦ embedSplitSpatial hd (F r)) t := by
  apply frontSpatial_eq_realOrbit_add_duhamel_of_classical f D c φ h₁ h₂ hd
    ((embedSplitSpatial hd).continuous.comp_continuousOn hv)
    ((embedSplitSpatial hd).continuous.comp_continuousOn hF)
    (hreg.embedSplitSpatial hd) _ ht
  intro r hr x
  have h := (realStateEmbeddingCLM : ℝ^n →L[ℝ] ℂ^n).hasFDerivAt.comp_hasDerivAt r
    (hpde r hr (transverse x) (horizontal x))
  simp only [Function.comp_apply]
  rw [frontSpatial_expression_embedSplitSpatial f D c φ hd (v r) (hreg.contDiff hr),
    embedSplitSpatial_apply]
  rw [← realStateEmbeddingCLM_apply, ← realStateEmbeddingCLM_apply, ← map_add]
  exact h

end

end Planarwave
