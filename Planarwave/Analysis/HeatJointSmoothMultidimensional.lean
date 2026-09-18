/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.HeatEquationMultidimensional
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-!
# Joint space-time smoothness of finite-dimensional heat flow

Spatial BUC derivatives and the semigroup law reduce each further space-time derivative to
another heat orbit with BUC data. This supplies the classical regularity required by the
Cole--Hopf construction in every transverse dimension.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ContDiff Laplacian

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Joint differentiability in Gaussian scale and position for data with a BUC derivative. -/
theorem differentiable_gaussianAverage_uncurry_of_hasFDerivAt (f : BUC E F)
    (g : BUC E (E →L[ℝ] F)) (hg : ∀ x, HasFDerivAt f (g x) x) :
    Differentiable ℝ (fun p : ℝ × E => ∫ z : E, f (p.2 + p.1 • z) ∂stdGaussian E) := by
  intro p
  let L : E → (ℝ × E →L[ℝ] E) := fun z =>
    ContinuousLinearMap.snd ℝ ℝ E +
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight z
  let K : (ℝ × E) → E → (ℝ × E →L[ℝ] F) :=
    fun q z => (g (q.2 + q.1 • z)).comp (L z)
  have hL : Continuous L := continuous_const.add
    (((ContinuousLinearMap.smulRightL ℝ (ℝ × E) E) (ContinuousLinearMap.fst ℝ ℝ E)).continuous)
  have hLbound (z : E) : ‖L z‖ ≤ 1 + ‖z‖ := by
    calc
      ‖L z‖ ≤ ‖ContinuousLinearMap.snd ℝ ℝ E‖ +
          ‖(ContinuousLinearMap.fst ℝ ℝ E).smulRight z‖ :=
        norm_add_le (ContinuousLinearMap.snd ℝ ℝ E) ((ContinuousLinearMap.fst ℝ ℝ E).smulRight z)
      _ ≤ 1 + ‖(ContinuousLinearMap.fst ℝ ℝ E).smulRight z‖ :=
        add_le_add (ContinuousLinearMap.norm_snd_le ℝ ℝ E) le_rfl
      _ = 1 + ‖z‖ := by rw [ContinuousLinearMap.norm_smulRight_apply]; simp
  have hKcont (q : ℝ × E) : Continuous (K q) :=
    (g.continuous.comp (by fun_prop)).clm_comp hL
  have hm (q : ℝ × E) : AEStronglyMeasurable (K q) (stdGaussian E) := by
    have : TopologicalSpace.PseudoMetrizableSpace (ℝ × E →L[ℝ] F) :=
      @PseudoEMetricSpace.pseudoMetrizableSpace (ℝ × E →L[ℝ] F) inferInstance
    exact (hKcont q).aestronglyMeasurable
  have hbound (q : ℝ × E) (z : E) : ‖K q z‖ ≤ ‖g‖ * (1 + ‖z‖) := by
    exact ((g (q.2 + q.1 • z)).opNorm_comp_le (L z)).trans
      (mul_le_mul (g.norm_apply_le _) (hLbound z) (norm_nonneg (L z)) (norm_nonneg g))
  have hdiff (q : ℝ × E) (z : E) :
      HasFDerivAt (fun r : ℝ × E => f (r.2 + r.1 • z)) (K q z) q := by
    have harg : HasFDerivAt (fun r : ℝ × E => r.2 + r.1 • z) (L z) q := by
      exact (hasFDerivAt_snd (𝕜 := ℝ) (p := q)).add
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).smul_const z)
    simpa only [Function.comp_def] using (hg (q.2 + q.1 • z)).comp q harg
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q z => f (q.2 + q.1 • z)) (F' := K)
    (bound := fun z : E => ‖g‖ * (1 + ‖z‖)) (s := univ) (μ := stdGaussian E)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun q => (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    ((integrable_const ‖f‖).mono' (f.continuous.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun z => f.norm_apply_le _))
    (hm p) (ae_of_all _ fun z q _ => hbound q z)
    (((integrable_const 1).add
      (IsGaussian.integrable_id : Integrable (id : E → E) (stdGaussian E)).norm).const_mul ‖g‖)
    (ae_of_all _ fun z q _ => hdiff q z)).differentiableAt

/-- Joint differentiability at positive time for arbitrary BUC data. -/
theorem differentiableAt_heatFlow_uncurry {a : ℝ} (ha : 0 < a) (f : BUC E F)
    (p : ℝ × E) (hp : 0 < p.1) :
    DifferentiableAt ℝ (fun q : ℝ × E => heatFlow a q.1 f q.2) p := by
  have hhalf : 0 < p.1 / 2 := by positivity
  let v := heatFlowBUC a (p.1 / 2) f
  let g := heatFDerivBUC ha hhalf f
  have hg : ∀ y, HasFDerivAt v (g y) y := fun y => hasFDerivAt_heatFlow ha hhalf f y
  have hs : DifferentiableAt ℝ (fun q : ℝ × E => heatScale a (q.1 - p.1 / 2)) p :=
    (hasDerivAt_heatScale ha (show 0 < p.1 - p.1 / 2 by linarith)).differentiableAt.comp p
      (f := fun q : ℝ × E => q.1 - p.1 / 2) (g := heatScale a)
      (differentiableAt_fst.sub_const (p.1 / 2))
  have h := (differentiable_gaussianAverage_uncurry_of_hasFDerivAt v g hg _).comp p
    (hs.prodMk differentiableAt_snd)
  apply h.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto p).eventually
    (Ioi_mem_nhds (show p.1 / 2 < p.1 by linarith))] with q hq
  change heatFlow a q.1 f q.2 = heatFlow a (q.1 - p.1 / 2) v q.2
  have hcoe : (v : E → F) = heatFlow a (p.1 / 2) f := funext (heatFlowBUC_apply _ _ f)
  rw [hcoe, heatFlow_add_time ha.le (sub_pos.mpr hq).le hhalf.le
    f.uniformContinuous f.norm_apply_le, sub_add_cancel]

/-- The joint derivative consists of the time heat operator and the spatial derivative. -/
theorem fderiv_heatFlow_uncurry_apply {a : ℝ} (ha : 0 < a) (f : BUC E F)
    (p : ℝ × E) (hp : 0 < p.1) (w : ℝ × E) :
    fderiv ℝ (fun q : ℝ × E => heatFlow a q.1 f q.2) p w =
      w.1 • (a • Δ (heatFlow a p.1 f) p.2) + fderiv ℝ (heatFlow a p.1 f) p.2 w.2 := by
  let J := fderiv ℝ (fun q : ℝ × E => heatFlow a q.1 f q.2) p
  have h := (differentiableAt_heatFlow_uncurry ha f p hp).hasFDerivAt
  have ht := h.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have htval : J (1, 0) = a • Δ (heatFlow a p.1 f) p.2 :=
    ht.unique (hasDerivAt_heatFlow_time ha hp f p.2)
  have hx := h.comp p.2 ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) p.2))
  have hxval : J (0, w.2) = fderiv ℝ (heatFlow a p.1 f) p.2 w.2 :=
    by
      rw [(hasFDerivAt_heatFlow ha hp f p.2).fderiv]
      exact DFunLike.congr_fun (hx.unique (hasFDerivAt_heatFlow ha hp f p.2)) w.2
  have hw : w = w.1 • (1, 0) + (0, w.2) := by ext <;> simp
  change J w = _
  conv_lhs => rw [hw]
  rw [map_add, map_smul, htval, hxval]

/-- A positive-time heat orbit has two successive BUC Fréchet derivatives. -/
theorem exists_buc_fderivatives_heatFlow {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (f : BUC E F) :
    ∃ (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F)),
      (∀ x, HasFDerivAt (heatFlow a t f) (g x) x) ∧ (∀ x, HasFDerivAt g (h x) x) := by
  have hhalf : 0 < t / 2 := by positivity
  let v := heatFlowBUC a (t / 2) f
  let g₀ := heatFDerivBUC ha hhalf f
  have hg₀ : ∀ y, HasFDerivAt v (g₀ y) y := fun y => hasFDerivAt_heatFlow ha hhalf f y
  have hsplit : heatFlow a t f = heatFlow a (t / 2) v := by
    have hcoe : (v : E → F) = heatFlow a (t / 2) f := funext (heatFlowBUC_apply _ _ f)
    rw [hcoe, heatFlow_add_time ha.le hhalf.le hhalf.le f.uniformContinuous f.norm_apply_le,
      add_halves]
  refine ⟨heatFlowBUC a (t / 2) g₀, heatFDerivBUC ha hhalf g₀, ?_, ?_⟩
  · intro x
    rw [hsplit]
    exact hasFDerivAt_heatFlow_of_hasFDerivAt a (t / 2) v g₀ hg₀ x
  · intro x
    exact hasFDerivAt_heatFlow ha hhalf g₀ x

/-- Trace contraction on continuous bilinear maps, expressed in an orthonormal basis. -/
def laplacianTraceCLM : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F :=
  ∑ i : Fin (Module.finrank ℝ E),
    (ContinuousLinearMap.apply ℝ F (stdOrthonormalBasis ℝ E i)).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) (stdOrthonormalBasis ℝ E i))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The Laplacian is the trace contraction of the second Fréchet derivative. -/
theorem laplacian_eq_trace_fderiv (f : E → F) (x : E) :
    Δ f x = laplacianTraceCLM (fderiv ℝ (fderiv ℝ f) x) := by
  simp [laplacianTraceCLM, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Heat averaging commutes with bounded linear operations on the values. -/
theorem heatFlow_postcompCLM (a t : ℝ) (L : F →L[ℝ] G) (f : BUC E F) (x : E) :
    heatFlow a t (BUC.postcompCLM L f) x = L (heatFlow a t f x) :=
  L.integral_comp_comm (integrable_comp_add_heatScale f.continuous ‖f‖ f.norm_apply_le x)

/-- With two BUC derivatives, the Laplacian commutes with heat averaging. -/
theorem laplacian_heatFlow_eq_heatFlow (a t : ℝ) (f : BUC E F)
    (g : BUC E (E →L[ℝ] F)) (h : BUC E (E →L[ℝ] E →L[ℝ] F))
    (hg : ∀ x, HasFDerivAt f (g x) x) (hh : ∀ x, HasFDerivAt g (h x) x) (x : E) :
    Δ (heatFlow a t f) x =
      heatFlow a t (BUC.postcompCLM (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] F) (F := F)
        (laplacianTraceCLM (E := E) (F := F)) h) x := by
  rw [laplacian_eq_trace_fderiv, fderiv_heatFlow_of_hasFDerivAt a t f g hg,
    fderiv_heatFlow_of_hasFDerivAt a t g h hh, heatFlow_postcompCLM]

/-- Joint space-time smoothness to every finite order at positive times. -/
theorem contDiffOn_nat_heatFlow_uncurry (k : ℕ) {a : ℝ} (ha : 0 < a) (f : BUC E F) :
    ContDiffOn ℝ k (fun p : ℝ × E => heatFlow a p.1 f p.2) (Ioi 0 ×ˢ univ) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set E)) := isOpen_Ioi.prod isOpen_univ
  induction k generalizing f with
  | zero =>
    apply contDiffOn_zero.mpr
    intro p hp
    exact (differentiableAt_heatFlow_uncurry ha f p hp.1).continuousAt.continuousWithinAt
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hopen]
    refine ⟨fun p hp => (differentiableAt_heatFlow_uncurry ha f p hp.1).differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_clm_apply]
    intro w p hp
    have hppos : 0 < p.1 := hp.1
    have hr : 0 < p.1 / 2 := by positivity
    let v := heatFlowBUC a (p.1 / 2) f
    obtain ⟨g, h, hg, hh⟩ := exists_buc_fderivatives_heatFlow ha hr f
    have hg' : ∀ x, HasFDerivAt v (g x) x := hg
    let gw : BUC E F := BUC.postcompCLM (ContinuousLinearMap.apply ℝ F w.2) g
    let lh : BUC E F := BUC.postcompCLM (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] F) (F := F)
      (laplacianTraceCLM (E := E) (F := F)) h
    let shift : ℝ × E → ℝ × E := fun q => (q.1 - p.1 / 2, q.2)
    have hshift : ContDiff ℝ k shift := by dsimp [shift]; fun_prop
    have hmem : shift p ∈ Ioi 0 ×ˢ (univ : Set E) :=
      ⟨by change 0 < p.1 - p.1 / 2; linarith, mem_univ _⟩
    have hcg : ContDiffAt ℝ k (fun q : ℝ × E => heatFlow a (q.1 - p.1 / 2) gw q.2) p :=
      ((ih gw).contDiffAt (hopen.mem_nhds hmem)).comp p hshift.contDiffAt
    have hch : ContDiffAt ℝ k (fun q : ℝ × E => heatFlow a (q.1 - p.1 / 2) lh q.2) p :=
      ((ih lh).contDiffAt (hopen.mem_nhds hmem)).comp p hshift.contDiffAt
    have hJ := ((hch.const_smul a).const_smul w.1).add hcg
    apply (hJ.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [(continuous_fst.tendsto p).eventually
      (Ioi_mem_nhds (show p.1 / 2 < p.1 by linarith))] with q hq
    have hqpos : 0 < q.1 := hr.trans hq
    rw [fderiv_heatFlow_uncurry_apply ha f q hqpos]
    have hsplit : heatFlow a q.1 f = heatFlow a (q.1 - p.1 / 2) v := by
      have hcoe : (v : E → F) = heatFlow a (p.1 / 2) f := funext (heatFlowBUC_apply _ _ f)
      rw [hcoe, heatFlow_add_time ha.le (sub_pos.mpr hq).le hr.le
        f.uniformContinuous f.norm_apply_le, sub_add_cancel]
    rw [hsplit, laplacian_heatFlow_eq_heatFlow a _ v g h hg' hh,
      fderiv_heatFlow_of_hasFDerivAt a _ v g hg']
    congr 1
    exact (heatFlow_postcompCLM a _ (ContinuousLinearMap.apply ℝ F w.2) g q.2).symm

/-- Heat flow is jointly smooth in time and space throughout the positive-time half-space. -/
theorem contDiffOn_infty_heatFlow_uncurry {a : ℝ} (ha : 0 < a) (f : BUC E F) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => heatFlow a p.1 f p.2) (Ioi 0 ×ˢ univ) :=
  contDiffOn_infty.mpr fun k => contDiffOn_nat_heatFlow_uncurry k ha f

end

end Planarwave
