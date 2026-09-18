/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Planarwave.Analysis.BUC2
public import Planarwave.Analysis.BUCBilinear
public import Planarwave.Analysis.ChallengeBridge
public import Planarwave.Analysis.ClosedOperator
public import Planarwave.Analysis.ClosedOperatorFromResolvent
public import Planarwave.Analysis.ColeHopf
public import Planarwave.Analysis.ColeHopfEvolution
public import Planarwave.Analysis.ColeHopfLaplacian
public import Planarwave.Analysis.ColeHopfPDE
public import Planarwave.Analysis.ComplexBUC2
public import Planarwave.Analysis.ComplexFrequencyCriticalSpectrum
public import Planarwave.Analysis.ComplexFrequencySemigroupBounds
public import Planarwave.Analysis.ConcreteFredholm
public import Planarwave.Analysis.ConvectiveHeatSemigroup
public import Planarwave.Analysis.DiagonalDiffusionSemigroup
public import Planarwave.Analysis.FredholmProjection
public import Planarwave.Analysis.FrontCoefficient
public import Planarwave.Analysis.FrontEigenvalueBranch
public import Planarwave.Analysis.HeatSemigroup
public import Planarwave.Analysis.HeatEquationOneDimensional
public import Planarwave.Analysis.HeatSmoothing
public import Planarwave.Analysis.HeatSmoothingMultidimensional
public import Planarwave.Analysis.HeatSmoothMultidimensional
public import Planarwave.Analysis.HeatEquationMultidimensional
public import Planarwave.Analysis.HeatJointSmoothMultidimensional
public import Planarwave.Analysis.LongitudinalOperator
public import Planarwave.Analysis.PhaseFunctional
public import Planarwave.Analysis.PositiveDiffusion
public import Planarwave.Analysis.ProfileProjection
public import Planarwave.Analysis.Semigroup
public import Planarwave.Analysis.SemigroupOperations
public import Planarwave.Analysis.SimpleEigenvaluePerturbation
public import Planarwave.Analysis.SimpleSpectralProjection
public import Planarwave.Analysis.TranslationMode
public import Planarwave.Analysis.TransverseOperatorBridge
public import Planarwave.Analysis.TwoEndedBUC
public import Planarwave.Coordinates

@[expose] public section

/-!
# Formalization map for Theorem 1.6

This module records the dependency order of the proof in de Rijk--van Winden.  It intentionally
contains no replacement theorem or additional hypothesis: every analytic item below is a proof
obligation that must eventually be discharged from the hypotheses in `Challenge.lean`.

The paper proof is being formalized in this order:

1. Proposition 2.1: the transverse Fourier symbol has a simple critical eigenvalue
   `lambda_c ξ = -d_perp * ‖ξ‖² + O(‖ξ‖⁴)` and projection `P_ξ = P_0 + O(‖ξ‖²)`.
2. Lemmas 2.2--2.4: complex-frequency bounds for the longitudinal analytic semigroups.
3. Propositions 3.4--3.5 and Theorem 3.1: contour-shifted kernel bounds and the full semigroup
   decomposition into transverse heat flow along `φ'` plus an `O((1+t)⁻¹)` remainder.
4. Section 4: inverse modulation, the exact perturbation equation, and delayed phase forcing.
5. Section 5: Cole--Hopf estimates and the nonlinear bootstrap.
6. Section 6: continuation of the reaction--diffusion solution and comparison of the forced and
   unforced viscous Hamilton--Jacobi phases.

The local analytic portion of step 1 is now formalized: `FrontEigenvalueBranch` constructs the
normalized local eigenpair, proves bounded-window separation of the remaining transverse
spectrum, and establishes the scalar-parameter Taylor estimates.  `SimpleSpectralProjection`
constructs the corresponding holomorphic rank-one spectral splitting.  Finally,
`ComplexFrequencyCriticalSpectrum` pulls this construction back along the paper's holomorphic
quadratic form `lambda_0(ξ) = ∑ i, ξ_i^2`, giving the multidimensional holomorphic eigenvalue and
projection together with `lambda_c(ξ) = -d_perp * lambda_0(ξ) + O(‖ξ‖^4)` and
`P_ξ = P_0 + O(‖ξ‖^2)`.  The remaining part of the critical-spectrum stage is the unbounded
spectral-parameter separation needed for the subsequent semigroup estimates.

The formalization of step 2 has also begun in the order used in Lemma 2.2.  The scalar
convective heat evolution is now a strongly continuous contraction semigroup.  Diagonalizing the
positive diffusion matrix gives a finite product semigroup with the paper's strictly positive
Gaussian damping rate.  Moreover,
`Re lambda_0(ξ₀ + i ξ₁) = ‖ξ₀‖^2 - ‖ξ₁‖^2` gives the elementary heat-multiplier bound, and the
bounded contour-shift perturbation satisfies the paper's Young-inequality estimate (2.4).
Abstract conjugation of the diagonal semigroup, with its condition-number bound, is also proved.
The remaining work in that lemma is to instantiate the function-space change of coordinates
with the concrete diffusion eigenbasis, identify the longitudinal generators, and apply the
bounded perturbation theorem.

The initial phase required by the nonlinear theorem is constructed in `ChallengeInitialPhase`.
Its defining longitudinal integral is integrable on each transverse slice, and the resulting
phase belongs to transverse BUC. Its BUC norm is at most `E_0 * ∫ z, ‖ψ z‖`, and the phase map
depends Lipschitz continuously on the initial datum in the supremum norm. This supplies initial
data for the viscous Hamilton--Jacobi construction.

`ColeHopfEvolution` constructs that phase evolution, proves its initial value, semigroup law,
uniform-in-time norm bound, strong time continuity, and uniform continuity on finite time slabs.
The inverse cancellation calculation in `ColeHopfPDE` turns classical heat solutions into vHJ
solutions. `HeatDirectionalSmoothing` identifies the multidimensional Fréchet derivative using
orthogonal Gaussian splitting. `HeatSmoothMultidimensional` proves that this derivative is BUC,
with a dimension-independent norm bound, and obtains all-order spatial smoothing by splitting
the heat semigroup. `HeatEquationMultidimensional` proves the classical heat equation, and
`HeatJointSmoothMultidimensional` proves joint positive-time smoothness, all for Banach-valued
data in arbitrary finite dimension. Consequently
`Planarwave.isVHJSolution_challengePhaseEvolution` proves the full phase solution predicate for
every `d ≥ 2`. `Planarwave.exists_challengePhaseSolution` packages the solution, its exact initial
integral, and its uniform smallness bound. This completes unforced-phase existence; the
reaction--diffusion construction and nonlinear approximation estimate remain outstanding.

## Milestones still needed for the challenge theorem

The phase construction is an independent prerequisite for the final comparison. Completing it
does not discharge the spectral and nonlinear stages listed above. The next main-line target is
the longitudinal generator/semigroup identification, followed by these concrete milestones:

* Prove uniform complex-frequency semigroup and resolvent estimates, including separation for
  unbounded spectral parameters. Local holomorphic eigenpairs alone do not give these bounds.
* Construct the full spatial semigroup and its decomposition into the transverse heat evolution
  on the translation mode plus a decaying remainder, with the derivative estimates needed by
  Duhamel's formula.
* Construct local classical reaction--diffusion solutions from BUC perturbations, together with
  a continuation criterion; derive the exact inverse-modulation and phase-forcing equations.
* Close the nonlinear bootstrap using those linear estimates and Cole--Hopf bounds, keeping the
  constants uniform over `0 ≤ E_0 ≤ ε`, and use continuation to obtain a global solution.
* Compare the forced modulation phase to the unforced solution constructed here, obtaining
  `C * E_0 * (E_0 + (1+t)⁻¹ * log (2+t))`, then assemble the unchanged challenge statement.

Each milestone must be proved from the original hypotheses. No auxiliary regularity or decay
assumption should be added to `vHJ_approximates_planar_front` to bypass these obligations.

The imported modules provide the foundational objects for those steps: a Banach space of bounded
uniformly continuous functions, a fixed-domain closed-operator resolvent, the Gaussian heat
contraction, the scalar Cole--Hopf equivalence, and the coordinate splitting used in the theorem.
-/

namespace Planarwave

/-- Names of the paper-level obligations, in their mathematical dependency order.  This finite
index is useful for documentation and does not assert any unproved mathematics. -/
inductive PaperProofStage
  | criticalSpectrum
  | symbolSemigroupBounds
  | fullSemigroupDecomposition
  | inverseModulation
  | nonlinearBootstrap
  | globalContinuation
  deriving DecidableEq, Repr

/-- The next paper-level stage after a completed one, when there is one. -/
def PaperProofStage.next : PaperProofStage → Option PaperProofStage
  | .criticalSpectrum => some .symbolSemigroupBounds
  | .symbolSemigroupBounds => some .fullSemigroupDecomposition
  | .fullSemigroupDecomposition => some .inverseModulation
  | .inverseModulation => some .nonlinearBootstrap
  | .nonlinearBootstrap => some .globalContinuation
  | .globalContinuation => none

end Planarwave
