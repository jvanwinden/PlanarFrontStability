/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

@[expose] public section

/-!
# Bounded uniformly continuous functions

This file bundles bounded uniformly continuous functions.  The norm and metric are inherited from
`BoundedContinuousFunction`, so the norm is the supremum norm.  In particular, this is a Banach
space whenever the codomain is a Banach space.

The basic pre- and postcomposition operations below are intended to support convolution operators
and, in particular, the heat semigroup on Euclidean space.
-/

open Bornology Filter Function Set Topology
open scoped BoundedContinuousFunction Topology

universe u v w

noncomputable section

/-- A bounded uniformly continuous function from `α` to `E`.

The bounded continuous function is stored explicitly so that the supremum norm and the existing
`BoundedContinuousFunction` API can be reused. -/
structure BUC (α : Type u) (E : Type v) [UniformSpace α] [PseudoMetricSpace E] where
  /-- The underlying bounded continuous function. -/
  toBCF : α →ᵇ E
  /-- The underlying function is uniformly continuous. -/
  uniformContinuous' : UniformContinuous (toBCF : α → E)

namespace BUC

variable {α : Type u} {β : Type v} {E : Type w}

section Basic

variable [UniformSpace α] [PseudoMetricSpace E]

instance instFunLike : FunLike (BUC α E) α E where
  coe f := f.toBCF
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact BoundedContinuousFunction.ext fun x ↦ congr_fun h x

/-- Reinterpret a bounded uniformly continuous function as a bounded continuous function. -/
instance instCoeBCF : Coe (BUC α E) (α →ᵇ E) := ⟨toBCF⟩

@[simp]
theorem coe_toBCF (f : BUC α E) : (f.toBCF : α → E) = f := rfl

@[ext]
theorem ext {f g : BUC α E} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

theorem toBCF_injective : Injective (toBCF : BUC α E → α →ᵇ E) := fun _ _ h ↦ by
  ext x
  exact DFunLike.congr_fun h x

/-- A bounded uniformly continuous function is uniformly continuous. -/
protected theorem uniformContinuous (f : BUC α E) : UniformContinuous (f : α → E) :=
  f.uniformContinuous'

/-- A bounded uniformly continuous function is continuous. -/
protected theorem continuous (f : BUC α E) : Continuous (f : α → E) :=
  f.uniformContinuous.continuous

/-- The range of a bounded uniformly continuous function is bounded. -/
theorem isBounded_range (f : BUC α E) : Bornology.IsBounded (range f) :=
  f.toBCF.isBounded_range

/-- The image of any set under a bounded uniformly continuous function is bounded. -/
theorem isBounded_image (f : BUC α E) (s : Set α) : Bornology.IsBounded (f '' s) :=
  f.toBCF.isBounded_image s

/-- Constant bounded uniformly continuous functions. -/
def const (α : Type u) [UniformSpace α] (e : E) : BUC α E where
  toBCF := BoundedContinuousFunction.const α e
  uniformContinuous' := uniformContinuous_const

@[simp]
theorem const_apply (e : E) (x : α) : const α e x = e := rfl

/-- Precomposition by a uniformly continuous function. -/
def comp {β : Type v} [UniformSpace β] (f : BUC α E) (g : β → α)
    (hg : UniformContinuous g) : BUC β E where
  toBCF := f.toBCF.compContinuous ⟨g, hg.continuous⟩
  uniformContinuous' := f.uniformContinuous.comp hg

@[simp]
theorem comp_apply {β : Type v} [UniformSpace β] (f : BUC α E) (g : β → α)
    (hg : UniformContinuous g) (x : β) : f.comp g hg x = f (g x) := rfl

@[simp]
theorem comp_id (f : BUC α E) : f.comp id uniformContinuous_id = f := by
  ext
  rfl

theorem comp_comp {γ : Type*} [UniformSpace β] [UniformSpace γ] (f : BUC α E)
    (g : β → α) (hg : UniformContinuous g) (h : γ → β) (hh : UniformContinuous h) :
    (f.comp g hg).comp h hh = f.comp (g ∘ h) (hg.comp hh) := by
  ext
  rfl

end Basic

section Algebra

variable [UniformSpace α] [NormedAddCommGroup E]

instance instZero : Zero (BUC α E) := ⟨⟨0, uniformContinuous_const⟩⟩

@[simp]
theorem coe_zero : ⇑(0 : BUC α E) = 0 := rfl

@[simp]
theorem zero_apply (x : α) : (0 : BUC α E) x = 0 := rfl

instance instAdd : Add (BUC α E) :=
  ⟨fun f g ↦ ⟨f.toBCF + g.toBCF, f.uniformContinuous.add g.uniformContinuous⟩⟩

@[simp]
theorem coe_add (f g : BUC α E) : ⇑(f + g) = f + g := rfl

@[simp]
theorem add_apply (f g : BUC α E) (x : α) : (f + g) x = f x + g x := rfl

instance instSMulNat : SMul ℕ (BUC α E) where
  smul n f := nsmulRec n f

@[simp]
theorem coe_nsmul (f : BUC α E) : ∀ n : ℕ, ⇑(n • f) = n • ⇑f
  | 0 => by rw [show (0 : ℕ) • f = 0 from rfl, zero_nsmul, coe_zero]
  | n + 1 => by rw [show (n + 1) • f = n • f + f from rfl, succ_nsmul, coe_add, coe_nsmul]

instance instNeg : Neg (BUC α E) := ⟨fun f ↦ ⟨-f.toBCF, f.uniformContinuous.neg⟩⟩

@[simp]
theorem coe_neg (f : BUC α E) : ⇑(-f) = -f := rfl

@[simp]
theorem neg_apply (f : BUC α E) (x : α) : (-f) x = -f x := rfl

instance instSub : Sub (BUC α E) :=
  ⟨fun f g ↦ ⟨f.toBCF - g.toBCF, f.uniformContinuous.sub g.uniformContinuous⟩⟩

@[simp]
theorem coe_sub (f g : BUC α E) : ⇑(f - g) = f - g := rfl

@[simp]
theorem sub_apply (f g : BUC α E) (x : α) : (f - g) x = f x - g x := rfl

theorem coe_zsmulRec (f : BUC α E) : ∀ z : ℤ, ⇑(zsmulRec (· • ·) z f) = z • ⇑f
  | Int.ofNat n => by rw [zsmulRec, Int.ofNat_eq_natCast, coe_nsmul, natCast_zsmul]
  | Int.negSucc n => by rw [zsmulRec, negSucc_zsmul, coe_neg, coe_nsmul]

instance instSMulInt : SMul ℤ (BUC α E) where
  smul z f := zsmulRec (· • ·) z f

@[simp]
theorem coe_zsmul (z : ℤ) (f : BUC α E) : ⇑(z • f) = z • ⇑f := by
  exact coe_zsmulRec f z

instance instAddCommGroup : AddCommGroup (BUC α E) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun f n ↦ coe_nsmul f n) fun _ _ ↦ coe_zsmul _ _

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance instSMul : SMul 𝕜 (BUC α E) :=
  ⟨fun c f ↦ ⟨c • f.toBCF, f.uniformContinuous.const_smul c⟩⟩

@[simp]
theorem coe_smul (c : 𝕜) (f : BUC α E) : ⇑(c • f) = c • ⇑f := rfl

@[simp]
theorem smul_apply (c : 𝕜) (f : BUC α E) (x : α) : (c • f) x = c • f x := rfl

instance instModule : Module 𝕜 (BUC α E) := fast_instance%
  Function.Injective.module 𝕜
    ⟨⟨(⇑), coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

end Algebra

section PseudoMetric

variable [UniformSpace α] [PseudoMetricSpace E]

/-- The uniform metric inherited from bounded continuous functions. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (BUC α E) :=
  PseudoMetricSpace.induced toBCF inferInstance

@[simp]
theorem dist_toBCF_eq_dist (f g : BUC α E) : dist f.toBCF g.toBCF = dist f g := rfl

theorem dist_apply_le (f g : BUC α E) (x : α) : dist (f x) (g x) ≤ dist f g :=
  BoundedContinuousFunction.dist_coe_le_dist x

/-- Evaluation at a fixed point is `1`-Lipschitz. -/
theorem lipschitz_eval (x : α) : LipschitzWith 1 fun f : BUC α E ↦ f x :=
  LipschitzWith.mk_one fun f g ↦ dist_apply_le f g x

/-- Convergence in `BUC` is uniform convergence. -/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι → BUC α E} {f : BUC α E}
    {l : Filter ι} : Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i ↦ (F i : α → E)) f l := by
  simpa only [Metric.tendsto_nhds] using!
    (@BoundedContinuousFunction.tendsto_iff_tendstoUniformly _ _ _ _ _
      (fun i ↦ (F i).toBCF) f.toBCF l)

/-- The inclusion of `BUC` into bounded continuous functions is an isometry. -/
theorem isometry_toBCF : Isometry (toBCF : BUC α E → α →ᵇ E) := fun _ _ ↦ rfl

end PseudoMetric

section Metric

variable [UniformSpace α] [MetricSpace E]

/-- The uniform metric is a genuine metric when the codomain metric is. -/
noncomputable instance instMetricSpace : MetricSpace (BUC α E) :=
  MetricSpace.induced toBCF toBCF_injective inferInstance

/-- Uniformly continuous bounded continuous functions form a closed subset. -/
theorem isClosed_range_toBCF :
    IsClosed (range (toBCF : BUC α E → α →ᵇ E)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u f hu huf
  have huc : ∀ n, UniformContinuous (u n : α → E) := by
    intro n
    obtain ⟨g, hg⟩ := hu n
    rw [← hg]
    exact g.uniformContinuous
  have hunif : TendstoUniformly (fun n ↦ (u n : α → E)) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp huf
  exact ⟨⟨f, hunif.uniformContinuous (Eventually.of_forall huc).frequently⟩, rfl⟩

/-- `BUC α E` is complete whenever `E` is complete. -/
instance instCompleteSpace [CompleteSpace E] : CompleteSpace (BUC α E) :=
  (completeSpace_iff_isComplete_range isometry_toBCF.isUniformInducing).mpr
    isClosed_range_toBCF.isComplete

end Metric

section Norm

variable [UniformSpace α] [NormedAddCommGroup E]

/-- The supremum norm inherited from bounded continuous functions. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (BUC α E) := fast_instance%
  NormedAddCommGroup.induced _ _
    (⟨⟨toBCF, rfl⟩, fun _ _ ↦ rfl⟩ : BUC α E →+ α →ᵇ E) toBCF_injective

@[simp]
theorem norm_toBCF_eq_norm (f : BUC α E) : ‖f.toBCF‖ = ‖f‖ := rfl

/-- Point evaluation is bounded by the supremum norm. -/
theorem norm_apply_le (f : BUC α E) (x : α) : ‖f x‖ ≤ ‖f‖ :=
  f.toBCF.norm_coe_le_norm x

/-- Characterization of a supremum-norm upper bound. -/
theorem norm_le {f : BUC α E} {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C :=
  BoundedContinuousFunction.norm_le hC

/-- The norm is the supremum of the pointwise norms. -/
theorem norm_eq_iSup_norm (f : BUC α E) : ‖f‖ = ⨆ x, ‖f x‖ :=
  f.toBCF.norm_eq_iSup_norm

theorem norm_const_le (e : E) : ‖const α e‖ ≤ ‖e‖ :=
  BoundedContinuousFunction.norm_const_le e

@[simp]
theorem norm_const_eq [Nonempty α] (e : E) : ‖const α e‖ = ‖e‖ :=
  BoundedContinuousFunction.norm_const_eq e

/-- Precomposition does not increase the supremum norm. -/
theorem norm_comp_le {β : Type v} [UniformSpace β] (f : BUC α E) (g : β → α)
    (hg : UniformContinuous g) : ‖f.comp g hg‖ ≤ ‖f‖ :=
  f.toBCF.norm_compContinuous_le ⟨g, hg.continuous⟩

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance instNormedSpace : NormedSpace 𝕜 (BUC α E) where
  norm_smul_le c f := by
    change ‖c • f.toBCF‖ ≤ ‖c‖ * ‖f.toBCF‖
    exact norm_smul_le c f.toBCF

/-- The inclusion into bounded continuous functions as a continuous linear map. -/
def toBCFCLM : BUC α E →L[𝕜] α →ᵇ E :=
  LinearMap.mkContinuous
    { toFun := toBCF
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun f ↦ by simp

@[simp]
theorem toBCFCLM_apply (f : BUC α E) :
    toBCFCLM (𝕜 := 𝕜) f = f.toBCF := rfl

/-- Evaluation at a point as a continuous linear map. -/
def evalCLM (x : α) : BUC α E →L[𝕜] E :=
  (BoundedContinuousFunction.evalCLM 𝕜 x).comp toBCFCLM

@[simp]
theorem evalCLM_apply (x : α) (f : BUC α E) :
    evalCLM (𝕜 := 𝕜) x f = f x := rfl

/-- Constant functions as a continuous linear map. -/
def constCLM (α : Type u) [UniformSpace α] : E →L[𝕜] BUC α E :=
  LinearMap.mkContinuous
    { toFun := const α
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
    1 fun e ↦ by simpa using norm_const_le (α := α) e

@[simp]
theorem constCLM_apply (e : E) : constCLM (𝕜 := 𝕜) α e = const α e := rfl

/-- Precomposition by a uniformly continuous map as a continuous linear map. -/
def compCLM {β : Type v} [UniformSpace β] (g : β → α)
    (hg : UniformContinuous g) : BUC α E →L[𝕜] BUC β E :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.comp g hg
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
    1 fun f ↦ by simpa using norm_comp_le f g hg

@[simp]
theorem compCLM_apply {β : Type v} [UniformSpace β] (g : β → α)
    (hg : UniformContinuous g) (f : BUC α E) : compCLM (𝕜 := 𝕜) g hg f = f.comp g hg := rfl

end Norm

section Postcomp

variable [UniformSpace α]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Postcomposition by a continuous linear map. -/
noncomputable def postcompCLM (L : E →L[𝕜] F) : BUC α E →L[𝕜] BUC α F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦
        ⟨L.compLeftContinuousBounded α f.toBCF, L.uniformContinuous.comp f.uniformContinuous⟩
      map_add' := fun f g ↦ by
        ext x
        change L (f x + g x) = L (f x) + L (g x)
        exact L.map_add _ _
      map_smul' := fun c f ↦ by
        ext x
        change L (c • f x) = c • L (f x)
        exact L.map_smul _ _ }
    ‖L‖ fun f ↦ by
      change ‖L.compLeftContinuousBounded α f.toBCF‖ ≤ ‖L‖ * ‖f.toBCF‖
      apply BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2
      intro x
      exact L.le_opNorm_of_le (f.norm_apply_le x)

@[simp]
theorem postcompCLM_apply (L : E →L[𝕜] F) (f : BUC α E) (x : α) :
    postcompCLM L f x = L (f x) := rfl

/-- The standard supremum-norm bound for postcomposition by a continuous linear map. -/
theorem norm_postcompCLM_apply_le (L : E →L[𝕜] F) (f : BUC α E) :
    ‖postcompCLM L f‖ ≤ ‖L‖ * ‖f‖ := by
  change ‖L.compLeftContinuousBounded α f.toBCF‖ ≤ ‖L‖ * ‖f.toBCF‖
  apply BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2
  intro x
  exact L.le_opNorm_of_le (f.norm_apply_le x)

end Postcomp

section Translate

variable [NormedAddCommGroup α] [NormedAddCommGroup E]

/-- Translation of the argument, with `translate a f x = f (x - a)`. -/
def translate (a : α) (f : BUC α E) : BUC α E :=
  f.comp (fun x ↦ x - a) (uniformContinuous_id.sub uniformContinuous_const)

@[simp]
theorem translate_apply (a : α) (f : BUC α E) (x : α) : translate a f x = f (x - a) := rfl

@[simp]
theorem translate_zero (f : BUC α E) : translate 0 f = f := by
  ext
  simp

theorem translate_add (a b : α) (f : BUC α E) :
    translate a (translate b f) = translate (a + b) f := by
  ext x
  simp [sub_sub]

theorem norm_translate_le (a : α) (f : BUC α E) : ‖translate a f‖ ≤ ‖f‖ :=
  norm_comp_le f _ _

@[simp]
theorem norm_translate (a : α) (f : BUC α E) : ‖translate a f‖ = ‖f‖ := by
  apply le_antisymm (norm_translate_le a f)
  calc
    ‖f‖ = ‖translate (-a) (translate a f)‖ := by
      congr 1
      ext x
      simp
    _ ≤ ‖translate a f‖ := norm_translate_le (-a) (translate a f)

/-- Translation is strongly continuous on bounded uniformly continuous functions. -/
theorem tendsto_translate_zero (f : BUC α E) :
    Tendsto (fun a ↦ translate a f) (nhds 0) (nhds f) := by
  rw [tendsto_iff_tendstoUniformly]
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp f.uniformContinuous ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : α) hδ] with a ha
  intro x
  apply hmod
  simpa [Metric.mem_ball, dist_eq_norm] using ha

/-- For fixed `f`, translation depends continuously on the translation vector. -/
theorem continuous_translate (f : BUC α E) : Continuous fun a ↦ translate a f := by
  rw [continuous_iff_continuousAt]
  intro a
  have hsub : Tendsto (fun b : α ↦ b - a) (nhds a) (nhds 0) := by
    simpa using (tendsto_id.sub tendsto_const_nhds :
      Tendsto (fun b : α ↦ b - a) (nhds a) (nhds (a - a)))
  have hzero := (tendsto_translate_zero (translate a f)).comp hsub
  show Tendsto (fun b ↦ translate b f) (nhds a) (nhds (translate a f))
  convert hzero using 1 <;> simp [Function.comp_def, translate_add]

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- Translation as a continuous linear map. -/
noncomputable def translateCLM (a : α) : BUC α E →L[𝕜] BUC α E :=
  compCLM (𝕜 := 𝕜) (fun x ↦ x - a) (uniformContinuous_id.sub uniformContinuous_const)

@[simp]
theorem translateCLM_apply (a : α) (f : BUC α E) : translateCLM (𝕜 := 𝕜) a f = translate a f :=
  rfl

end Translate

end BUC
