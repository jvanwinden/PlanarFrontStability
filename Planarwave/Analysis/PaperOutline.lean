/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Planarwave.Analysis.BUCJointContinuity
public import Planarwave.Analysis.BUCSpacetimeCalculus
public import Planarwave.Analysis.BUCMixedDerivatives
public import Planarwave.Analysis.BUCPointwiseTimeDerivative
public import Planarwave.Analysis.BUCSpacetimeRegularity
public import Planarwave.Analysis.BUCSpacetimeBootstrap
public import Planarwave.Analysis.BoundedSmoothDerivatives
public import Planarwave.Analysis.BUCSpatialRegularity
public import Planarwave.Analysis.BUCSpatialBounds
public import Planarwave.Analysis.BUCSpatialRegularityLocal
public import Planarwave.Analysis.BUCSpatialRegularityWithin
public import Planarwave.Analysis.BUCSpatialComposition
public import Planarwave.Analysis.BUCLinearPullback
public import Planarwave.Analysis.BUCNonlinearHigher
public import Planarwave.Analysis.BUCAutonomousODEBounds
public import Planarwave.Analysis.BUCCompactSupport
public import Planarwave.Analysis.BUC2
public import Planarwave.Analysis.BUCBilinear
public import Planarwave.Analysis.BUCFirstJet
public import Planarwave.Analysis.ScalarFirstJet
public import Planarwave.Analysis.VectorFirstJet
public import Planarwave.Analysis.BUCFDerivCoordinates
public import Planarwave.Analysis.BUCNonlinear
public import Planarwave.Analysis.BUCPartialDerivatives
public import Planarwave.Analysis.BUCPartialDerivativeContinuity
public import Planarwave.Analysis.BUCOperatorConvolution
public import Planarwave.Analysis.BUCConvolutionComposition
public import Planarwave.Analysis.BUCVolterraUniqueness
public import Planarwave.Analysis.BUCSlices
public import Planarwave.Analysis.ChallengeBridge
public import Planarwave.Analysis.ClassicalODELimit
public import Planarwave.Analysis.CompatibleLocalTrajectories
public import Planarwave.Analysis.ClosedOperator
public import Planarwave.Analysis.ClosedOperatorFromResolvent
public import Planarwave.Analysis.ClosedOperatorResolvent
public import Planarwave.Analysis.ClosedOperatorRestriction
public import Planarwave.Analysis.ColeHopf
public import Planarwave.Analysis.ColeHopfEvolution
public import Planarwave.Analysis.ColeHopfInverseDerivative
public import Planarwave.Analysis.ColeHopfInverseSecondDerivative
public import Planarwave.Analysis.ColeHopfInverseHigherBounds
public import Planarwave.Analysis.ColeHopfInverseHigherRegularity
public import Planarwave.Analysis.ColeHopfLaplacian
public import Planarwave.Analysis.ColeHopfPDE
public import Planarwave.Analysis.IntegralGronwall
public import Planarwave.Analysis.EndpointNormBound
public import Planarwave.Analysis.IntegrableDecayGronwall
public import Planarwave.Analysis.IntegrablePolynomialConvolution
public import Planarwave.Analysis.LogarithmicDecayWeights
public import Planarwave.Analysis.DerivativeInterpolation
public import Planarwave.Analysis.NinthDerivativeInterpolation
public import Planarwave.Analysis.TrackingInterpolation
public import Planarwave.Analysis.SpatialTrackingInterpolation
public import Planarwave.Analysis.NonlinearBootstrapPowers
public import Planarwave.Analysis.IntegrableLogarithmicDecay
public import Planarwave.Analysis.ImprovedColeHopfSource
public import Planarwave.Analysis.ForcedColeHopfBounds
public import Planarwave.Analysis.ForcedColeHopfPhase
public import Planarwave.Analysis.ForcedColeHopfComparison
public import Planarwave.Analysis.ForcedColeHopfExistence
public import Planarwave.Analysis.ForcedColeHopfRegularity
public import Planarwave.Analysis.ForcedColeHopfFirstDerivativeBounds
public import Planarwave.Analysis.ForcedColeHopfSecondRegularity
public import Planarwave.Analysis.ForcedColeHopfSecondDerivativeBounds
public import Planarwave.Analysis.ForcedColeHopfDerivativeDecay
public import Planarwave.Analysis.ForcedColeHopfClassical
public import Planarwave.Analysis.ForcedPhaseClassical
public import Planarwave.Analysis.ForcedPhaseFirstDerivativeBounds
public import Planarwave.Analysis.ForcedPhaseSecondDerivativeBounds
public import Planarwave.Analysis.ForcedPhaseDerivativeDecay
public import Planarwave.Analysis.ForcedPhaseComparison
public import Planarwave.Analysis.HeatDuhamel
public import Planarwave.Analysis.HeatDuhamelDerivative
public import Planarwave.Analysis.HeatGradientOperator
public import Planarwave.Analysis.HeatDuhamelSmoothing
public import Planarwave.Analysis.HeatDuhamelGradientContinuity
public import Planarwave.Analysis.HeatHigherDuhamelSmoothing
public import Planarwave.Analysis.HeatOrbitHigherBounds
public import Planarwave.Analysis.SemilinearHeatRegularity
public import Planarwave.Analysis.FiniteHeatSystemRegularity
public import Planarwave.Analysis.MatrixReactionDiffusionRegularity
public import Planarwave.Analysis.MatrixReactionDiffusionPositiveJets
public import Planarwave.Analysis.MatrixReactionDiffusionPositiveClosedJets
public import Planarwave.Analysis.HeatDerivativeDecay
public import Planarwave.Analysis.HeatDuhamelTimeRegularity
public import Planarwave.Analysis.HeatMildClassical
public import Planarwave.Analysis.NonlinearVolterra
public import Planarwave.Analysis.NonlinearVolterraUniqueness
public import Planarwave.Analysis.FiniteHeatSystemLocalExistence
public import Planarwave.Analysis.FiniteHeatSystemUniqueness
public import Planarwave.Analysis.FiniteHeatSystemContinuation
public import Planarwave.Analysis.FiniteHeatSystemBoundedContinuation
public import Planarwave.Analysis.FiniteHeatSystemMaximal
public import Planarwave.Analysis.FiniteHeatSystemClassical
public import Planarwave.Analysis.MatrixReactionDiffusionLocalExistence
public import Planarwave.Analysis.MatrixReactionDiffusionUniqueness
public import Planarwave.Analysis.ReactionDiffusionSpacetime
public import Planarwave.Analysis.ReactionDiffusionSmooth
public import Planarwave.Analysis.MatrixReactionDiffusionSpacetime
public import Planarwave.Analysis.MatrixReactionDiffusionContinuation
public import Planarwave.Analysis.MatrixReactionDiffusionLocalClassical
public import Planarwave.Analysis.MatrixReactionDiffusionMaximal
public import Planarwave.Analysis.MatrixReactionDiffusionGlobal
public import Planarwave.Analysis.HeatDuhamelBilinearBounds
public import Planarwave.Analysis.HeatVolterra
public import Planarwave.Analysis.HeatVolterraInvariant
public import Planarwave.Analysis.HeatLinearRegularity
public import Planarwave.Analysis.ComplexBUC2
public import Planarwave.Analysis.ComplexBUC2Density
public import Planarwave.Analysis.ComplexFrequencyCriticalSpectrum
public import Planarwave.Analysis.ComplexFrequencySemigroupBounds
public import Planarwave.Analysis.ComplexTimeSector
public import Planarwave.Analysis.ComplexVolterra
public import Planarwave.Analysis.ComplexDysonSeries
public import Planarwave.Analysis.ConcreteFredholm
public import Planarwave.Analysis.ConvectiveHeatSemigroup
public import Planarwave.Analysis.ConvectiveHeatGeneratorMultidimensional
public import Planarwave.Analysis.ConvectiveHeatSmoothing
public import Planarwave.Analysis.ConvectiveHeatSmoothingMultidimensional
public import Planarwave.Analysis.CoordinateGaussian
public import Planarwave.Analysis.CoordinateLaplacian
public import Planarwave.Analysis.DiagonalDiffusionSemigroup
public import Planarwave.Analysis.DiagonalHeatFourier
public import Planarwave.Analysis.DiagonalGaussianConvolution
public import Planarwave.Analysis.DiffusionSemigroup
public import Planarwave.Analysis.DiffusionGenerator
public import Planarwave.Analysis.DiffusionSmoothing
public import Planarwave.Analysis.DiffusionAnalytic
public import Planarwave.Analysis.DelayedHeatForcing
public import Planarwave.Analysis.DelayedHeatForcingSmoothing
public import Planarwave.Analysis.DelayedHeatForcingRegularity
public import Planarwave.Analysis.DelayedHeatForcingDerivative
public import Planarwave.Analysis.DelayedHeatForcingFirstDerivativeBounds
public import Planarwave.Analysis.DelayedHeatForcingSecondDerivative
public import Planarwave.Analysis.DelayedHeatForcingSecondDerivativeBounds
public import Planarwave.Analysis.DelayedHeatForcingDecay
public import Planarwave.Analysis.DelayedHeatForcingHigherDerivativeBounds
public import Planarwave.Analysis.DelayedHeatForcingHigherRegularity
public import Planarwave.Analysis.DelayedHeatForcingImprovedDecay
public import Planarwave.Analysis.DelayedHeatForcingCancellation
public import Planarwave.Analysis.DelayedPolynomialDecay
public import Planarwave.Analysis.HeatCriticalResidualDecay
public import Planarwave.Analysis.TemporalCutoff
public import Planarwave.Analysis.LinearCutoffJet
public import Planarwave.Analysis.ScalingVariation
public import Planarwave.Analysis.FredholmProjection
public import Planarwave.Analysis.FrontCoefficient
public import Planarwave.Analysis.FrontAdjointEquation
public import Planarwave.Analysis.FrontAdjointRegularization
public import Planarwave.Analysis.FrontAdjointEstimates
public import Planarwave.Analysis.FrontAdjointRegularity
public import Planarwave.Analysis.FrontNonlinearity
public import Planarwave.Analysis.InverseModulationNonlinearityContinuity
public import Planarwave.Analysis.FrontNonlinearityContinuity
public import Planarwave.Analysis.FrontInterpolatedNonlinearity
public import Planarwave.Analysis.FrontModulationPDE
public import Planarwave.Analysis.FrontPhysicalModulationPDE
public import Planarwave.Analysis.FrontPhysicalModulationDifferentiability
public import Planarwave.Analysis.FrontPhysicalDuhamel
public import Planarwave.Analysis.FrontPhysicalTrackingEstimate
public import Planarwave.Analysis.FrontPhysicalNonlinearSource
public import Planarwave.Analysis.FrontTrackingInitialZero
public import Planarwave.Analysis.FrontTrackingSystem
public import Planarwave.Analysis.FrontTrackingInitialBound
public import Planarwave.Analysis.FrontTrackingInitialSystem
public import Planarwave.Analysis.FrontExistingPhaseBounds
public import Planarwave.Analysis.TrackingSmoothingCutoff
public import Planarwave.Analysis.FrontCutoffNonlinearityDecay
public import Planarwave.Analysis.FrontTrackingAPriori
public import Planarwave.Analysis.TrackingBootstrapContinuity
public import Planarwave.Analysis.FrontTrackingBootstrapClosure
public import Planarwave.Analysis.FrontDelayedForcingCausality
public import Planarwave.Analysis.FrontTrackingSourceCongruence
public import Planarwave.Analysis.FrontTrackingPhaseExtension
public import Planarwave.Analysis.FrontTrackingExtension
public import Planarwave.Analysis.FrontTrackingExistence
public import Planarwave.Analysis.FrontTrackingGlobal
public import Planarwave.Analysis.FrontTrackingVHJComparison
public import Planarwave.Analysis.ModulationHigherBounds
public import Planarwave.Analysis.ModulationContinuity
public import Planarwave.Analysis.ModulationSpatialRegularity
public import Planarwave.Analysis.FrontProfileHigherBounds
public import Planarwave.Analysis.FrontModulationHigherBounds
public import Planarwave.Analysis.FrontPhysicalModulationBounds
public import Planarwave.Analysis.FrontPhysicalModulationRegularity
public import Planarwave.Analysis.FrontPhysicalNormBound
public import Planarwave.Analysis.FrontRealProfileDerivatives
public import Planarwave.Analysis.FrontModulationSource
public import Planarwave.Analysis.FrontNonlinearDispersion
public import Planarwave.Analysis.FrontModulationProjection
public import Planarwave.Analysis.ModulationSourceDecay
public import Planarwave.Analysis.RealSpatialEmbedding
public import Planarwave.Analysis.RealSpatialEmbeddingRegularity
public import Planarwave.Analysis.FrontProjectedNonlinearity
public import Planarwave.Analysis.FrontSmoothedNonlinearityDecay
public import Planarwave.Analysis.FrontImprovedForcingDecay
public import Planarwave.Analysis.FrontPhaseComparison
public import Planarwave.Analysis.FrontVHJComparison
public import Planarwave.Analysis.FrontDelayedForcing
public import Planarwave.Analysis.FrontForcedPhase
public import Planarwave.Analysis.FrontForcedPhaseFirstDerivativeBounds
public import Planarwave.Analysis.FrontForcedPhaseSecondDerivativeBounds
public import Planarwave.Analysis.FrontForcedPhaseDerivativeDecay
public import Planarwave.Analysis.FrontTrackingDecay
public import Planarwave.Analysis.FrontForcingHigherDerivativeBounds
public import Planarwave.Analysis.FrontForcedColeHopfHigherBounds
public import Planarwave.Analysis.FrontForcedPhaseHigherBounds
public import Planarwave.Analysis.FrontEigenvalueBranch
public import Planarwave.Analysis.FrontLinearizedMild
public import Planarwave.Analysis.FrontLinearizedSemigroup
public import Planarwave.Analysis.FrontAllFrequencySemigroup
public import Planarwave.Analysis.FrontAnalyticSemigroup
public import Planarwave.Analysis.FrontCriticalSemigroup
public import Planarwave.Analysis.FrontFourierSymbol
public import Planarwave.Analysis.FrontFourierKernel
public import Planarwave.Analysis.FrontFourierContour
public import Planarwave.Analysis.FrontOffDiagonalKernel
public import Planarwave.Analysis.FrontKernelFrequencySplit
public import Planarwave.Analysis.FrontOnDiagonalKernel
public import Planarwave.Analysis.FrontKernelDecay
public import Planarwave.Analysis.FrontRemainderConvolution
public import Planarwave.Analysis.FrontFourierDecomposition
public import Planarwave.Analysis.FrontFourierDuhamel
public import Planarwave.Analysis.FrontFourierShortTime
public import Planarwave.Analysis.FrontDiffusionKernel
public import Planarwave.Analysis.FrontKernelVolterra
public import Planarwave.Analysis.FrontBoundedKernelVolterra
public import Planarwave.Analysis.FrontBoundedDuhamel
public import Planarwave.Analysis.FrontFourierInitial
public import Planarwave.Analysis.FrontFourierIdentification
public import Planarwave.Analysis.FrontSpatialDecay
public import Planarwave.Analysis.FrontSpatialRemainderDuhamelDecay
public import Planarwave.Analysis.FrontTrackingRemainderDecay
public import Planarwave.Analysis.FrontPhaseRemainderEstimate
public import Planarwave.Analysis.FrontTrackingCriticalDecomposition
public import Planarwave.Analysis.FrontPhaseTrackingEstimate
public import Planarwave.Analysis.FrontPhaseHigherTrackingEstimate
public import Planarwave.Analysis.LogarithmicConvolution
public import Planarwave.Analysis.FrontSpatialAnalytic
public import Planarwave.Analysis.FrontSpatialSemigroup
public import Planarwave.Analysis.FrontSpatialGenerator
public import Planarwave.Analysis.FrontClassicalDuhamel
public import Planarwave.Analysis.FrontSplitClassicalDuhamel
public import Planarwave.Analysis.FrontSpatialTranslation
public import Planarwave.Analysis.FrontSpatialFourierDuhamel
public import Planarwave.Analysis.FrontSpatialKernel
public import Planarwave.Analysis.FourierContourShift
public import Planarwave.Analysis.FrontLowFrequencyTaylor
public import Planarwave.Analysis.FrontLowFrequencySemigroup
public import Planarwave.Analysis.FrontComplementSemigroup
public import Planarwave.Analysis.FrontHighFrequencySemigroup
public import Planarwave.Analysis.FrontMidFrequencySemigroup
public import Planarwave.Analysis.FrontCompactSemigroupBounds
public import Planarwave.Analysis.FrontSpectralSemigroup
public import Planarwave.Analysis.FrontLaplaceResolvent
public import Planarwave.Analysis.FrontSectorialResolvent
public import Planarwave.Analysis.FrontSpectralSeparation
public import Planarwave.Analysis.GaussianFourierKernel
public import Planarwave.Analysis.GaussianFourierDuhamel
public import Planarwave.Analysis.GaussianFourierConvolution
public import Planarwave.Analysis.GaussianHeatKernel
public import Planarwave.Analysis.GaussianFrequencySplit
public import Planarwave.Analysis.GaussianKernelDecay
public import Planarwave.Analysis.HeatSemigroup
public import Planarwave.Analysis.HeatDivergenceSmoothing
public import Planarwave.Analysis.HeatEquationOneDimensional
public import Planarwave.Analysis.HeatSmoothing
public import Planarwave.Analysis.HeatSmoothingMultidimensional
public import Planarwave.Analysis.HeatSmoothMultidimensional
public import Planarwave.Analysis.HeatHigherDerivativeBounds
public import Planarwave.Analysis.HeatHigherRegularity
public import Planarwave.Analysis.HeatHigherDuhamelBounds
public import Planarwave.Analysis.ForcedColeHopfHigherRegularity
public import Planarwave.Analysis.ForcedColeHopfHigherBounds
public import Planarwave.Analysis.HeatEquationMultidimensional
public import Planarwave.Analysis.HeatJointSmoothMultidimensional
public import Planarwave.Analysis.HolomorphicTimeExtension
public import Planarwave.Analysis.HolomorphicIntegral
public import Planarwave.Analysis.HorizontalContourShift
public import Planarwave.Analysis.LongitudinalOperator
public import Planarwave.Analysis.L1Smoothing
public import Planarwave.Analysis.L1Mollification
public import Planarwave.Analysis.L1DerivativeInterpolation
public import Planarwave.Analysis.L1DerivativeBoundedness
public import Planarwave.Analysis.L1EllipticEstimate
public import Planarwave.Analysis.LipschitzAELimit
public import Planarwave.Analysis.LongitudinalPairing
public import Planarwave.Analysis.LongitudinalPairingDerivative
public import Planarwave.Analysis.LongitudinalClosedness
public import Planarwave.Analysis.PhaseFunctional
public import Planarwave.Analysis.PiContourShift
public import Planarwave.Analysis.PositiveDiffusion
public import Planarwave.Analysis.ProfileProjection
public import Planarwave.Analysis.ProjectedNonlinearity
public import Planarwave.Analysis.Semigroup
public import Planarwave.Analysis.SemigroupGenerator
public import Planarwave.Analysis.SemigroupSmoothing
public import Planarwave.Analysis.SemigroupTaylor
public import Planarwave.Analysis.SemigroupHolomorphic
public import Planarwave.Analysis.SemigroupSector
public import Planarwave.Analysis.SemigroupRotation
public import Planarwave.Analysis.SectorialResolvent
public import Planarwave.Analysis.SemigroupGeneratorDensity
public import Planarwave.Analysis.SemigroupUniqueness
public import Planarwave.Analysis.SemigroupVariationOfConstants
public import Planarwave.Analysis.SemigroupIntertwining
public import Planarwave.Analysis.SemigroupRestriction
public import Planarwave.Analysis.SemigroupComplementDecay
public import Planarwave.Analysis.SemigroupSpectralDamping
public import Planarwave.Analysis.SemigroupEigenvector
public import Planarwave.Analysis.SemigroupDuhamel
public import Planarwave.Analysis.SemigroupVolterraSeries
public import Planarwave.Analysis.SemigroupPerturbation
public import Planarwave.Analysis.SemigroupParameterAnalytic
public import Planarwave.Analysis.SemigroupParameterContinuity
public import Planarwave.Analysis.SemigroupAnalyticPerturbation
public import Planarwave.Analysis.SemigroupPerturbationGenerator
public import Planarwave.Analysis.SemigroupPerturbationBound
public import Planarwave.Analysis.SemigroupPerturbationComposition
public import Planarwave.Analysis.SemigroupPerturbationIntertwining
public import Planarwave.Analysis.SemigroupCompactBounds
public import Planarwave.Analysis.SemigroupCompactSpectralBounds
public import Planarwave.Analysis.SemigroupRescale
public import Planarwave.Analysis.SemigroupLaplace
public import Planarwave.Analysis.SemigroupLaplaceMoment
public import Planarwave.Analysis.SemigroupLaplaceInversion
public import Planarwave.Analysis.SemigroupSpectralGrowth
public import Planarwave.Analysis.ResolventVerticalBounds
public import Planarwave.Analysis.ResolventContour
public import Planarwave.Analysis.VerticalContourShift
public import Planarwave.Analysis.SemigroupClosedOperator
public import Planarwave.Analysis.SemigroupOperations
public import Planarwave.Analysis.SimpleEigenvaluePerturbation
public import Planarwave.Analysis.SimpleSpectralProjection
public import Planarwave.Analysis.SimpleSpectralRestriction
public import Planarwave.Analysis.SpatialDiffusionSemigroup
public import Planarwave.Analysis.SpatialDiffusionSmoothing
public import Planarwave.Analysis.InverseModulationCoordinates
public import Planarwave.Analysis.InverseModulationNonlinearity
public import Planarwave.Analysis.InverseModulationPDE
public import Planarwave.Analysis.ModulationChainRule
public import Planarwave.Analysis.ModulationProfileDerivatives
public import Planarwave.Analysis.SpatialDiffusionFourier
public import Planarwave.Analysis.SpatialHeatFourier
public import Planarwave.Analysis.SpectralTaylorEstimate
public import Planarwave.Analysis.TaylorAnalytic
public import Planarwave.Analysis.TranslationMode
public import Planarwave.Analysis.TransverseOperatorBridge
public import Planarwave.Analysis.TwoEndedBUC
public import Planarwave.Coordinates

@[expose] public section

/-!
# Formalization map for Theorem 1.6

This module records the dependency order of the proof in de Rijk--van Winden.
The complete theorem is proved in the top-level `Solution.lean` as
`Planarwave.vHJ_approximates_planar_front_proved`. The protected
`Challenge.lean` was moved to the top level without content changes. `Comparator.lean` checks that the new
theorem has exactly the original theorem's type and reports only
`propext`, `Classical.choice`, and `Quot.sound` as its axioms.

The formalization follows the paper in this order:

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
`P_ξ = P_0 + O(‖ξ‖^2)`. `FrontSpectralSeparation` now removes the bounded-window restriction:
the uniform sectorial enclosure excludes large spectral parameters in a right half-plane,
and the existing compact-window argument handles the remainder. This proves Proposition
2.1(1)'s separation of every noncritical spectral point at small complex frequencies,
as well as the unbounded-window statement in the challenge's semantic transverse spectrum.

The complex-frequency semigroup estimates of step 2 are now proved, following Lemmas 2.2--2.4.
The scalar
convective heat evolution is now a strongly continuous contraction semigroup.  Diagonalizing the
positive diffusion matrix gives a finite product semigroup with the paper's strictly positive
Gaussian damping rate.  Moreover,
`Re lambda_0(ξ₀ + i ξ₁) = ‖ξ₀‖^2 - ‖ξ₁‖^2` gives the elementary heat-multiplier bound, and the
bounded contour-shift perturbation satisfies the paper's Young-inequality estimate (2.4).
`DiffusionEigenbasis` and `DiffusionSemigroup` instantiate this conjugation on longitudinal BUC
using the actual complexified diffusion eigenbasis. The resulting semigroup has the uniform
Gaussian operator-norm bound, and its right derivative at zero on `ComplexBUC2` is exactly
`D v'' + c v' - q D v`, in the BUC norm. Positive-time orbits lie in `ComplexBUC2`; spatial
derivatives commute with the flow, which preserves this domain and solves the principal
evolution equation there. `ComplexBUC2Density` proves that the domain is dense in BUC.
`SemigroupGenerator` proves the closed-graph and integral characterizations of a C₀ generator;
heat regularization then identifies its full graph with the closure of the principal
differential-operator graph. `BUCInterpolation` and `LongitudinalClosedness` now prove the
elliptic graph-norm estimate by absorbing the drift into the second derivative. Consequently
`DiffusionGenerator` proves full generator-domain equality: the principal generator has exactly
the `ComplexBUC2` domain and the stated differential expression. It also proves closedness of
the full longitudinal pencil at every complex parameter without a spectral assumption.

The quantitative principal smoothing step is also complete. `ConvectiveHeatSmoothing` proves
the scalar first- and second-derivative bounds in BUC norm and absorbs the generator's Fourier
damping factor into the Gaussian exponential. `DiffusionSmoothing` transports this calculation
through the same eigenbasis to obtain bounded operators `A_q S_q(t)` with `‖A_q S_q(t)‖ ≤ C/t`
for `0 < t ≤ 1`, uniformly over `q ≥ 0`. `SemigroupSmoothing` proves that bounded positive-time
generator regularization gives local operator-norm Lipschitz estimates, operator-norm time
derivatives, and smoothness of every finite order. These results are instantiated for the actual
principal diffusion semigroup, with its time derivative identified with the exact longitudinal
differential expression and bounded by the same `C/t`. This supplies quantitative real-time
regularity.

The principal evolution now also has a genuine holomorphic time extension. `SemigroupTaylor`
expresses higher derivatives using powers of `A S(r)` and proves factorial derivative bounds
on intervals separated from zero. `TaylorAnalytic` uses the Banach-valued integral remainder
to prove convergence to the actual real function, for positive and negative increments, then
constructs its complex power series extension. `DiffusionAnalytic` applies this to the matrix
diffusion semigroup on disks of radius `η * min t 1`, with one `η > 0` for all positive times and
all nonnegative Fourier parameters. `HolomorphicTimeExtension` proves agreement on overlapping
disks by the identity principle and glues them into a unique extension on their union. This
common open domain contains a fixed-angle wedge near zero and remains in the right half-plane.
Real analyticity of the principal semigroup is proved explicitly. The Taylor construction also
retains a geometric-series norm bound. Combining it with the uniform real-time diffusion bound
gives a uniformly bounded complex extension on the union of disks. `SemigroupHolomorphic`
proves its real-shift and small-complex-time semigroup laws, then obtains strong continuity at
zero by approximation with positive real-time orbits; no operator-norm continuity at zero is
assumed. `ComplexTimeSector` supplies the open convex sector geometry. `SemigroupSector` glues
the time-subdivision formulas `g(z/n)^n` on increasing truncated sectors and proves that the
result is independent of the subdivision. It satisfies the full complex semigroup law, strong
continuity at the vertex, and an exponential operator bound throughout the sector.
`DiffusionAnalytic.exists_uniform_frontDiffusion_holomorphic_sector` applies all of this to the
actual principal diffusion semigroups with one sector and common constants for every `q ≥ 0`.
The sectorial resolvent estimates are obtained below by rotating the full semigroups.

For the bounded-perturbation step, `SemigroupDuhamel` constructs the Volterra integral operator
on continuous paths. `SemigroupVolterraSeries` proves the factorial bound on its powers and
convergence of its Neumann series on every finite time interval. This supplies unique mild
trajectories and a bounded linear solution map. `FrontLinearizedMild` specializes the construction
to the actual multiplication operator `f'(φ)`, proves its frequency-independent bound and exact
common-domain decomposition, and verifies Duhamel's formula and the initial value for the
resulting linearized-front trajectories. `SemigroupPerturbation` proves compatibility across
time horizons and uses the time-splitting identity and uniqueness to construct the perturbed
C₀ semigroup. `SemigroupPerturbationGenerator` proves that its generator has exactly the same
domain and equals `A + B`. `SemigroupPerturbationBound` retains the exponential weight in each
Volterra iterate and proves `‖T(t)‖ ≤ M exp ((ω + M ‖B‖) t)`, including negative `ω`.
`SemigroupGeneratorDensity` proves density of the generator domain using time-averaged orbits.
`SemigroupUniqueness` differentiates `T(t-r) S(r)x` on that domain to prove that the generator
determines the semigroup. This identifies successive bounded perturbations with perturbation
by their sum in `SemigroupPerturbationComposition`.
`FrontLinearizedSemigroup` instantiates these results for the reaction coefficient and proves
the uniform real-frequency bound (2.3). `FrontAllFrequencySemigroup` applies the bounded
perturbation theorem a second time to the contour shift, verifies its full pencil generator,
and absorbs half the real-frequency damping by Young's inequality. Its
`exists_front_allFrequency_bound` combines the resulting operator estimate with the scalar
heat-multiplier estimate, completing the bound in Lemma 2.2.

Analytic bounded perturbation is now proved for these actual semigroups.
`HolomorphicIntegral` derives differentiation under the parameter integral from local Cauchy
bounds and almost-everywhere holomorphy. `ComplexVolterra` applies this to the rescaled
operator-valued convolution, integrating over the open unit interval so that no operator-norm
continuity at time zero is assumed. Its norm estimate gains a power of time and the factor
`1/(n+1)`. `ComplexDysonSeries` iterates this estimate to obtain factorial bounds, local uniform
convergence, holomorphy of the sum, and `‖T(z)‖ ≤ M exp ((ω + M ‖B‖) ‖z‖)`. Its correction
to the free semigroup tends to zero in operator norm, which preserves strong continuity at
the sector vertex. `SemigroupAnalyticPerturbation` identifies every complex Dyson term on
positive real times with the previously constructed real Volterra iterate. The holomorphic
sum therefore extends `boundedPerturbation` itself and satisfies the full complex semigroup
law. `FrontAnalyticSemigroup` applies this first to the reaction multiplier with constants
uniform over `q ≥ 0`, then to the common-base pencil for every complex `q`. Consequently all
contour-frequency semigroups in Lemmas 2.3--2.4 are analytic on one common time sector.
The critical projection also commutes with their holomorphic extensions near zero frequency.
These analytic-generation and invariance results supply the sectorial and spectral-gap
decay arguments below.

`SemigroupRotation` restricts these extensions to complex time rays, proves strong continuity
at the vertex, and identifies the rotated generator with `ζ A` on exactly the original domain.
Both domain inclusions use interior holomorphic smoothing and the closed generator graph.
`SectorialResolvent` applies the Laplace inverse on each ray, including the precise sign and
scaling for the convention `A - z I`. Two fixed rays give a resolvent bound throughout
`Ω < Re z + a |Im z|`, with inverse-distance decay. `FrontSectorialResolvent` supplies these
constants uniformly over bounded sets of complex pencil parameters. It also proves that the
spectrum in each right half-plane is compact. `FrontSpectralSeparation` uses the uniform
wedge to complete the previously missing unbounded-parameter spectral separation.

The resolvent side of this connection is now explicit. `SemigroupRescale` proves that complex
exponential rescaling shifts the full generator without changing its domain. `SemigroupLaplace`
constructs the Laplace-transform inverse, proves both inverse identities using the closed
generator graph, and establishes `‖R(z)‖ ≤ M / (Re z - ω)` whenever `Re z > ω` for a growth bound
`M exp (ω t)`. `SemigroupClosedOperator` transfers this to the fixed `ComplexBUC2` domain and
accounts for the challenge's opposite sign convention `A - z I`. `FrontLaplaceResolvent` obtains
frequency-uniform right-half-plane resolvent estimates from Lemma 2.2, together with the concrete
semantic spectral bound `Re z ≤ C - μ k²`. `ClosedOperatorResolvent` proves openness of the
resolvent set, holomorphic dependence of the inverse, the resolvent identity, and the derivative
formula. The front resolvent is also proved jointly holomorphic in `(q,z)` at every invertible
point, in both graph-domain and ambient operator norm. Full perturbed analyticity and sectorial
bounds are supplied separately by the constructions above.

The converse spectral-to-growth step is now proved in `SemigroupSpectralGrowth`.
`ResolventVerticalBounds` combines compact-strip continuity with the sectorial tails to obtain
`‖R(β + i y)‖ ≤ C/(1+|y|)` and integrability of the resolvent square. `VerticalContourShift`
passes from Cauchy's theorem on finite rectangles to absolutely convergent vertical integrals,
proving that the horizontal edges vanish. `ResolventContour` applies this to `exp(t z) R(z)^2`
and obtains a constant times `exp(β t)` on the line `Re z = β`.
`SemigroupLaplaceMoment` identifies the squared Laplace resolvent with the transform of
`t S(t)` by integrating an orbit derivative. `SemigroupLaplaceInversion` applies Banach-valued
Fourier inversion, with its exact `2π` normalization, to recover the operator `t S(t)`.
Shifting this contour into a spectral gap and using the local semigroup bound near zero proves
that every rate strictly above the spectral bound is a valid semigroup growth rate. This is
proved from the generator relation and sectorial estimates, not assumed as a decay hypothesis.

The critical-mode part of Lemma 2.3 is now proved. `SemigroupEigenvector` derives exponential
evolution on a generator eigenspace. `FrontCriticalSemigroup` shows that the critical projection
takes values in the common domain and proves `Sξ(t) Pξ = exp (t λc(ξ)) Pξ` near zero frequency.
`SpectralTaylorEstimate` follows the paper's exponential-remainder and polynomial-absorption
estimates. `FrontLowFrequencyTaylor.exists_frontCriticalSemigroup_taylor_bound` combines these
with Proposition 2.1 to prove the concrete `M/t` Gaussian bound, with `μ = d_perp/4` and
`κ = 2 d_perp` on one uniformly chosen contour box. Complementary exponential decay is
proved separately by the restriction and uniformization argument below.
`SemigroupIntertwining` extends generator uniqueness to bounded intertwiners.
`FrontSpectralSemigroup` uses the common-domain spectral splitting to show that the critical
projection is a left eigenmap as well, commutes with the actual semigroup, and has invariant
kernel. It proves the corresponding commutation with the complementary projection on small
complex contour frequencies.

The complementary part of Lemma 2.3 is now proved as well. `SemigroupRestriction` constructs
the C₀ semigroup on the invariant kernel and identifies both inclusions of its generator
domain. `ClosedOperatorRestriction` restricts the closed graph-norm operator, proves that
ambient resolvents restrict without increasing their norm, and removes the critical
eigenvalue using the Fredholm kernel/range splitting. `SimpleSpectralRestriction` proves
that the projection fixes the entire critical kernel, not just the constructed eigenvector.
`SemigroupComplementDecay` applies the proved spectral-to-growth theorem on this subspace;
`FrontComplementSemigroup` obtains the paper's individual bound with rate `-θ/4` from the
original hypotheses.

For uniformization the complementary subspaces vary with frequency. `SemigroupSpectralDamping`
extends their evolutions to the fixed ambient BUC space by a common decaying exponential on
the critical eigenline. It proves that this is a bounded perturbation and leaves the
complementary evolution exactly unchanged. `SemigroupCompactSpectralBounds` then applies
the appendix lemma to this continuous compact family. `FrontLowFrequencySemigroup` obtains
the uniform rate `-θ/8` on a closed parameter neighborhood and the paper's complex contour box.
Its `exists_front_lowFrequency_bound` combines this with the Taylor bound on one common box,
using one positive prefactor, decay constant, and imaginary-frequency growth constant.
This completes both estimates of Lemma 2.3.

`FrontHighFrequencySemigroup` also completes the high-frequency portion of Lemma 2.4. It uses
the paper's threshold `sqrt (2 C / μ₀ + 1)` in (2.3), then treats the imaginary contour shift
as a bounded perturbation, and includes the scalar heat multiplier in the resulting bound.
`FrontMidFrequencySemigroup` now supplies the missing intermediate-frequency bound and completes
the whole of Lemma 2.4. It obtains individual real-frequency decay from the challenge's transverse
spectral gap and the proved spectral-to-growth theorem, then uniformizes on the compact annulus.
The real estimates are combined at the paper's high-frequency threshold before applying the
same imaginary-frequency bounded perturbation. Including the heat multiplier yields the full
estimate for every prescribed positive cutoff, every imaginary frequency, and all `t ≥ 0`.

The appendix's uniform-semigroup lemma is now proved in `SemigroupCompactBounds`, following
the bounded-perturbation neighborhood estimate, finite subcover, and maximum of finitely many
prefactors. It also retains a common exponential weight and allows continuously parametrized
compact families. `FrontCompactSemigroupBounds` identifies all real and complex longitudinal
semigroups as perturbations of the zero-frequency semigroup by `-q D`, using their full
generator graphs. It applies uniformization to the concrete compact frequency annulus and
proves the rate-splitting step in (2.9), conditional on the individual decay bounds. Those
hypotheses are now discharged by `FrontMidFrequencySemigroup`. The complementary low-frequency
family is handled by the restriction and fixed-space uniformization described above.

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
integral, and its uniform smallness bound. This completes unforced-phase existence;
`FrontTrackingGlobal` and `FrontTrackingVHJComparison` supply the physical
solution and nonlinear approximation estimate used in the final assembly.

The first steps of Section 3's Fourier kernel construction are now proved.
`SemigroupParameterAnalytic` proves entire operator-norm dependence on a bounded perturbation
coefficient: on each finite time interval the Volterra operator depends continuously linearly
on that coefficient, and the factorial estimate makes its complement invertible everywhere.
`FrontFourierSymbol` applies this to the complex-frequency pencil and constructs the entire
remainder symbol, including its all-frequency Gaussian bound from Lemma 2.2.

`GaussianFourierKernel` proves absolute convergence, the dimensional Gaussian mass bound,
and spatial continuity of Banach-valued inverse Fourier integrals under Gaussian domination.
`FrontFourierKernel` constructs the actual operator-valued remainder kernel at positive time
on every shifted real contour, proves its Gaussian bound and spatial norm-continuity, and
shows that applying it to a longitudinal slice and evaluating at `z` gives the paper's
pointwise inner integral. The normalization `(2π)⁻ᵐ` is not included, as in the definition of `H`.
`HorizontalContourShift` proves the one-dimensional Banach-valued Cauchy step by finite
rectangles and vanishing Gaussian vertical sides. `PiContourShift` lifts it to the full
transverse frequency space by Fubini and successive coordinate shifts, proving absolute
convergence on every intermediate contour. `FourierContourShift` includes the holomorphic
oscillatory factor and its extracted real exponential. `FrontFourierContour` applies this
to the actual remainder symbol and uses the volume-preserving Euclidean/product coordinate
identification to prove that every shifted kernel equals the original real-contour kernel.
This is a theorem from the original hypotheses, not an assumption in the kernel's definition.

`FrontOffDiagonalKernel` now proves the paper's off-diagonal proposition in both operator
norm and pointwise form. It takes exactly the paper's shift `η = x/(2 κ t)`, integrates the
frequency Gaussian, and splits the spatial exponential at the threshold `4 κ`, obtaining
the rate `min κ (8 κ)⁻¹`. The intermediate spatial Gaussian estimate also proves absolute
integrability of the operator-valued kernel at every positive time.

`GaussianFrequencySplit` and `FrontKernelFrequencySplit` now implement the paper's
three-term frequency decomposition: the mid/high-frequency Gaussian outside the cutoff
ball, the exponentially decaying complement inside the ball, and the critical Taylor
Gaussian. `GaussianKernelDecay` supplies the small-shift choice and scalar time estimates.
`FrontOnDiagonalKernel` follows the estimates on `T₁`, `T₂`, and `T₃` separately, choosing
`η = ε x/t` and retaining the spatial rate `ε/2`. It proves the on-diagonal proposition in
operator norm and pointwise form from the original front hypotheses.

`FrontKernelDecay` combines both spatial regions and integrates the common Gaussian,
proving that the kernel's spatial operator-norm integral is at most `C/t` for `t ≥ 1`.
`BUCOperatorConvolution` constructs operator-valued convolution directly in the BUC space,
with norm bounded by the kernel's `L¹` norm. `FrontRemainderConvolution` applies it to the
actual Fourier kernel, includes the normalization `(2π)⁻ᵐ`, proves the source-coordinate
outer-integral formula, and obtains the `C/t` operator and pointwise bounds. `BUCSlices`
embeds jointly BUC spatial data into transverse BUC families of longitudinal slices without
changing the supremum norm, so this estimate applies to the paper's spatial perturbations.
The Fourier representation identifying this convolution with the full spatial semigroup
remainder is now proved in `FrontFourierIdentification`, as detailed below.

The full spatial evolution is now constructed independently of that Fourier representation.
`ConvectiveHeatGeneratorMultidimensional` proves the right generator limit `a Δv + Dv b`
in the BUC norm, using the existing multidimensional heat regularity and the BUC-valued
fundamental theorem of calculus. `SpatialDiffusionSemigroup` evolves every diffusion
eigenvector coordinate by full-dimensional convective heat flow and conjugates back using
the actual diffusion matrix. It proves a uniform norm bound and the generator action on
twice BUC differentiable coordinate data.

The corresponding quantitative spatial smoothing is now proved as well.
`ConvectiveHeatSmoothingMultidimensional` differentiates successive half-time
Gaussian evolutions to produce BUC first and second Fréchet derivatives with
the bounds `‖v‖ / sqrt (2*a*t)` and `‖v‖ / (a*t)`. The same bounds hold after
translation. Trace contraction gives the full-dimensional short-time scalar
generator estimate, uniformly over diffusion rates bounded below by a positive
constant. `BUCFDerivCoordinates` transports these derivative fields through a
finite linear change of coordinates, preserving their quantitative bounds.
`SpatialDiffusionSmoothing` applies this to the actual diffusion eigenbasis:
the first two derivatives in the original state coordinates have the expected
Gaussian bounds, and the positive-time principal orbit is spatially smooth to
every order. It proves the principal generator's `C/t` operator bound and
identifies the actual operator-valued time derivative with `D Δ + b · ∇`.

`FrontSpatialSemigroup` adds the actual multiplication operator `f'(φ(horizontal x))` by
bounded perturbation. It proves the spatial Duhamel identity, the full generator-domain
perturbation identity, and exponential and short-time uniform norm bounds. The drift and
longitudinal coordinate are exactly those of the challenge's coordinate splitting.
`FrontSpatialGenerator` identifies the resulting generator with
`D Δ + c ∂z + f'(φ(z))` and proves that data with this classical generator formula are
dense in spatial BUC. This is supremum-norm density, not yet a graph-norm core theorem.
`SemigroupPerturbationIntertwining` transports bounded intertwiners through compatible
bounded perturbations; `FrontSpatialTranslation` applies it to prove that the constructed
full spatial semigroup commutes with every transverse translation. No Fourier representation
or decay estimate for this semigroup is assumed in these constructions.

`FrontSpatialAnalytic` upgrades the full-dimensional principal generator bound
to a holomorphic time sector, with the complex semigroup law and strong initial
limit, and then applies the proved bounded-perturbation theorem to the actual
reaction coefficient. Consequently the actual spatial front evolution is
analytic, and hence smooth, in positive real time in operator norm. The Cauchy
estimate in `SemigroupAnalyticSmoothing` proves `‖A S(t)‖ ≤ C/t` for the full
spatial linearized generator at short times. These time-generator bounds do not
by themselves assert high spatial derivative estimates for the reaction-perturbed
evolution or the nonlinear solution; those regularity steps still need proofs.

The Gaussian part of the Fourier representation is now identified exactly.
`GaussianHeatKernel` computes the inverse Fourier Gaussian with the paper's
normalization `(2π)⁻ᵐ`, proves that its nonnegative Lebesgue density has mass one,
and identifies that density with the independently defined heat measure by its
characteristic function. This proves the iterated Fourier representation of the
actual heat flow for arbitrary BUC Banach-valued data, without imposing spatial
integrability on the initial datum or interchanging non-absolutely convergent integrals.
`FrontFourierDecomposition` applies it to the actual translation-mode projection,
proving the second representation in Section 3. It constructs the full Fourier
convolution from the full longitudinal symbol, proves both inner-frequency and
outer-kernel integrability, and identifies this convolution with the genuine
critical heat evolution plus the previously constructed remainder. Its difference
from the critical heat evolution is consequently bounded by `C/t` for `t ≥ 1`.
`FrontFourierIdentification` now transfers this decomposition and remainder bound
to the independently constructed `frontSpatialC0Semigroup`.

The principal part of that identification is now proved, not assumed.
`CoordinateGaussian` proves the orthogonal splitting in the challenge's exact
coordinates, identifies the product Gaussian with the full spatial Gaussian,
and applies Fubini to factor full heat averaging. `SpatialHeatFourier` bundles
the norm-preserving spatial slicing map and proves the transverse Fourier formula
for scalar diffusion with the longitudinal drift. `DiagonalHeatFourier` justifies
passing a finite diffusion eigenbasis through the iterated Fourier integral:
it proves separate integrability of the frequency integrals and their spatial
integrals without claiming joint absolute integrability before cancellation.
`SpatialDiffusionFourier` applies this to the actual diffusion matrix and proves
`spatialDiffusionC0Semigroup_eq_fourierIntegral` for every spatial BUC datum.
`FrontSpatialFourierDuhamel` proves that slicing intertwines the actual spatial
reaction coefficient with the longitudinal multiplication operator, and rewrites
the independently constructed full semigroup's Duhamel equation using the proved
principal Fourier integral. The resulting time integrand is integrable in
longitudinal BUC; the zero-lag endpoint is handled as a null singleton, not by
asserting an ordinary inverse Fourier formula at time zero.
`SemigroupParameterContinuity` proves joint strong continuity in the bounded
coefficient, time, and initial datum from continuity in the uniform path norm;
operator-norm continuity at time zero is not asserted. `GaussianFourierDuhamel`
proves frequency-time Fubini under a Gaussian bound uniform in the time split.
`FrontFourierDuhamel` discharges those hypotheses for the actual longitudinal
semigroups: the factors at times `t-r` and `r` retain Gaussian decay at the total
time `t`. It proves the full Fourier kernel's inverse-transformed Duhamel identity
and absolute integrability of its time forcing in longitudinal BUC.
`FrontFourierShortTime` applies the same contour shift at all positive times,
retaining exponential growth; cancellation of the spatial and frequency Gaussian
masses gives a nonsingular exponential bound on the remainder kernel's spatial
mass and on both Fourier convolutions. This supplies the local uniform bound
near zero that cannot be obtained from the large-time `C/t` estimate alone.

The spatial operator-product identification is now proved as well.
`GaussianFourierConvolution` identifies a Gaussian frequency multiplier with
spatial convolution for Banach-valued amplitudes, justifying space-frequency
Fubini with the product of two integrable majorants. `DiagonalGaussianConvolution`
passes this identity through the finite diffusion eigenbasis and proves an
operator-kernel mass bound independent of the positive Gaussian scales.
`FrontDiffusionKernel` constructs the principal operator kernel using the actual
diffusion coordinates and longitudinal convective heat operators. Its Fourier
symbol is exactly the independently constructed principal semigroup, and its
spatial operator-norm mass is bounded uniformly over all positive times.
`FrontKernelVolterra` then identifies the inverse transform of `S₀(t-r,ξ) B S(r,ξ)`
with the ordered spatial convolution, with no commutativity assumption on `B`.
It proves the full Fourier kernel's spatial Volterra equation and time
integrability after spatial integration; endpoint identities are used only
inside the open time interval. `FrontSpatialKernel` identifies principal-kernel
convolution on actual spatial BUC slices with the spatial principal semigroup
and proves the full spatial evolution's convolution Volterra equation in the
iterated BUC norm. The full Fourier kernel also now has a nonsingular exponential
bound on its spatial operator-norm mass, strengthening the convolution-operator
bound for purposes of absolute spatial integration.

The bounded-data identification is now complete. `BUCConvolutionComposition`
proves ordered spatial Fubini in the full iterated BUC norm, without imposing
integrability on the datum. `FrontBoundedKernelVolterra` applies it to the actual
principal and full kernels and proves an absolute double-integral bound uniform
over the open Duhamel time interval. `FrontBoundedDuhamel` obtains joint strong
measurability from the continuous frequency integrand, proves time-space Bochner
integrability and Fubini, and derives the full Fourier convolution's pointwise
Volterra equation in longitudinal BUC. It also proves an `O(t)` estimate for
the difference from principal diffusion in the full iterated BUC norm.
`FrontFourierInitial` uses that estimate and the actual principal semigroup's
strong continuity to prove the correct initial limit on spatial BUC data.

`BUCVolterraUniqueness` proves the standard factorial iteration estimate for
locally bounded BUC-valued trajectories satisfying a pointwise Volterra equation.
`FrontFourierIdentification` checks integrability of both evaluated forcing
terms, the common bounded Volterra coefficient, and local uniform bounds for
both evolutions. Uniqueness identifies the full Fourier convolution with the
actual spatial semigroup, and hence proves its critical-heat-plus-remainder
decomposition. No strong continuity claim on arbitrary iterated-BUC families is
used to obtain this identification. `FrontSpatialDecay` then follows the paper's
short-time and long-time split to prove the all-time `C/(1+t)` remainder estimate,
including time zero, in the spatial supremum norm expressed via isometric
slices. It also proves the first iterated Fourier representation for the actual
spatial semigroup and its uniform operator-norm bound for all nonnegative times.

`LogarithmicConvolution` proves the borderline `α = γ = 1` time convolution
from `lem:convolution`, including its exact value
`2*log(1+t)/(2+t)` and the bound `2*log(2+t)/(1+t)`.
`FrontSpatialRemainderDuhamelDecay` applies it to the actual spatial semigroup
remainder, with the initial term included. A source bounded by `M/(1+t)`
gives the Step 3a bound `C*M*log(2+t)/(1+t)`. The module also identifies this
remainder in the full spatial Duhamel decomposition by strong continuity and
interchange of the bounded slice map with the time integral.

The source estimate needed here is now proved for the actual tracking source.
`FrontRealProfileDerivatives` recovers real BUC representatives of `φ'` and
`φ''` from the canonical translation-mode jet. `ModulationSourceDecay`
bundles the four terms of `eq:defNtilde`, proves continuity on continuous
paths, and bounds them separately by the triangle inequality. Squaring the
half-power gradient estimate gives full-power decay, and `M ≤ 1` absorbs
the extra amplitude. `FrontModulationSource` specializes the profiles to
`d_perp φ' - Dφ'`, `Dφ'' + (c/2)φ'`, and `φ'`. It proves the exact pointwise
formula and `eq:Ntildeest`, deriving the delayed forcing bound internally.
`RealSpatialEmbedding` transports real split-coordinate BUC data to the
complex spatial-semigroup space and proves exact preservation of its norm.
`FrontTrackingRemainderDecay` then proves `eq:west` for this source, including
the initial term and time zero, without assuming a separate full-source bound.
It also specializes the exact spatial Duhamel decomposition to these paths.
`FrontPhaseRemainderEstimate` constructs the classical phase and obtains its
weighted derivatives, the full source bound, and the logarithmic remainder
bound together, starting only from the supplied `5/4` nonlinear source bound
and small initial data. This joins the low-order part of Step 1 to Step 3a
for the same phase.

The critical contribution is now identified and estimated as well.
`FrontNonlinearDispersion` proves Lemma `lem:ndispersion` from the original
hypotheses: the parameter derivative of `φ(z/α)` is `-z φ'(z)`, and its
actual longitudinal equation has right side `-2 Dφ'' - cφ'`.
`LinearCutoffJet` and `ScalingVariation` justify pairing this variation
with the integrable adjoint using expanding smooth cutoffs and dominated
convergence. Normalization then gives `⟨ψ,Dφ''⟩ = -c/2` without any extra
localization assumptions. `FrontModulationProjection` applies this identity
and the definition of `d_perp` to prove the exact cancellation
`⟨ψ,Ntilde⟩ = ⟨ψ,N⟩ - g`. Its critical Duhamel amplitude equals the previously
estimated cancelled residual, so it inherits the `5/4` decay of `N`.
`FrontTrackingCriticalDecomposition` identifies the complex rank-one heat
evolution on real data with that real amplitude times the translation mode.
Commuting the fixed profile map with the time integral gives the exact
`ζ φ' + w` decomposition for the actual spatial-semigroup Duhamel solution.
Combining the two estimates proves `eq:vkeyest` in the spatial supremum
norm. `FrontPhaseTrackingEstimate` joins this with the constructed classical
phase, with constants and smallness chosen before the paths and horizon.
`FrontPhaseHigherTrackingEstimate` now retains the full uniform C⁹ phase
bound, all time-continuous spatial BUC derivative paths, and the Cole--Hopf
identity together with this same logarithmic spatial response estimate.
Only continuous `N` and its `5/4` decay bound are supplied; the phase bounds
and the full-source bound are proved. The later physical smoothing, tracking
construction, bootstrap closure, and global comparison modules discharge
these supplied-source hypotheses for the actual nonlinear solution.

The first nonlinear estimate, Lemma 4.1, is now proved.
`BUCNonlinear` constructs continuous nonlinear composition on BUC by compactness
of the value range. It bounds the second reaction derivative on a compact ball,
then applies the mean value estimate to the first derivative and the Taylor
remainder to prove a uniform quadratic bound on every fixed perturbation ball.
`InverseModulationNonlinearity` constructs the exact five-term expression in
`eq:defN`, preserving the mixed-term and forcing signs, and estimates all terms
in the spatial supremum norm. `BUCPartialDerivatives` extracts the longitudinal
first and second derivatives and the transverse-longitudinal mixed derivative
from genuine BUC Frechet derivative fields, with the required norm bounds.
`FrontNonlinearity` specializes the result to the original reaction, diffusion,
front profile, and `d_perp`, using the end-state hypotheses for profile boundedness.
It identifies the bundled nonlinearity with the classical derivative expression
and proves the paper's quadratic-plus-`C²` estimate uniformly over the fixed-size
perturbation ball. No extra Taylor or coefficient bounds are assumed.

The interpolation in Step 4 is now proved. `DerivativeInterpolation` obtains
the adjustable-scale adjacent-order estimate for actual Fréchet derivatives
by the mean value theorem; isometric currying avoids a dimension-dependent
norm loss. `NinthDerivativeInterpolation` eliminates orders one through
eight and optimizes the scale, giving the `7/9` exponent for the C² norm
from a small supremum norm and a bounded ninth derivative. It also treats
zero initial amplitude, without dividing by that amplitude.

`TrackingInterpolation` uses the gap `7/9 - 3/4 = 1/36` to absorb the
logarithm and proves `eq:vestC2`, in the actual BUC two-jet norm used by
Lemma 4.1, wherever the uniform C⁹ bound is available. The constants and
smallness threshold precede the datum and time. `NonlinearBootstrapPowers`
then carries out Step 5's power counting. `FrontInterpolatedNonlinearity`
substitutes these estimates into the original front nonlinearity and
obtains `C*M^(7/4)*(1+t)^(-5/4)`, with no small first- or second-derivative
bound assumed. The uniform C⁹ bound is now transferred from bounded matrix
mild solutions to their actual inverse-modulated perturbations below.
The initial-time cutoff argument is supplied by
`FrontCutoffNonlinearityDecay`; `FrontTrackingAPriori` and
`FrontTrackingBootstrapClosure` combine it with physical smoothing and
close the actual nonlinear source estimate by continuity.

The higher-regularity transfer in Step 4 is now proved as well.
`BUCSpatialComposition` proves quantitative repeated chain rules for
uniformly continuous coordinate changes with genuine bounded derivative
fields, without requiring the coordinate map itself to be bounded.
`ModulationHigherBounds` applies this to the actual shear, whose derivative
is `I + (0, Dσ ∘ fst)`. The constants are independent of the translation
`c*t`. Its cutoff version transfers the bound on `χ • u` even when `χ = 0`,
without imposing smoothness on the uncut initial datum.

`BUCAutonomousODEBounds` proves all-order BUC derivative bounds for smooth
observables of a bounded autonomous ODE trajectory. `FrontProfileHigherBounds`
applies it to `(φ, φ')`, using the actual traveling-wave ODE, invertibility
of the original diffusion, and the already proved BUC translation mode.
Thus the fixed profile's C⁹ bound is derived from the original hypotheses,
not assumed when subtracting it in the modulation transfer.

`FrontModulationHigherBounds` combines this profile estimate with the phase
bound derived from the source bootstrap. Its constants and smallness
threshold precede all paths, data, and the time horizon. It obtains the
cut off perturbation's uniform C⁹ bound from the corresponding bound on
the reaction--diffusion slice alone. `SpatialTrackingInterpolation` then
constructs the genuine BUC first and second derivatives and obtains
`C*M^(3/4)*(1+t)^(-3/4)` for the actual cut off perturbation. The remaining
high-order input is the parabolic estimate for `χ • u`; it is not claimed
by these transfer and interpolation results alone. The later physical
modulation and Duhamel modules identify the logarithmic tracking bound and
nonlinear source with the coupled reaction--diffusion construction.

`FrontPhysicalModulationBounds` now supplies that high-order input from the
original matrix mild equation. `BUCLinearPullback` records the operator-norm
cost of changing from physical Euclidean coordinates to the max-norm split
coordinates, rather than identifying their norms. This gives both the
uniform cutoff C⁹ bound and the interpolated C² decay for the actual
physical inverse modulation. `FrontPhysicalNormBound` proves that a bound
on this perturbation bounds the physical solution by adding the fixed
profile norm, independently of the phase or its derivatives. The decay
estimate still requires a tracking bound for the same actual perturbation.

The derivative-gaining Duhamel step in that parabolic estimate is now proved.
`HeatGradientOperator` bundles the Gaussian spatial derivative as a bounded
linear BUC operator and proves joint strong continuity at positive heat ages.
`HeatDuhamelSmoothing` integrates its inverse-square-root singularity and
constructs the actual BUC derivative for a merely continuous BUC source,
with bound `2*C*sqrt(t)/sqrt(2*a)`. No derivative of the source is assumed.
`HeatDuhamelGradientContinuity` proves norm continuity of this derivative
through the initial time by reversing the integration variable and applying
dominated convergence. `HeatHigherDuhamelSmoothing` combines this gain with
commutation of existing derivatives: a time-continuous spatial `C^k` source
gives a time-continuous spatial `C^(k+1)` response, and all derivatives have
the common bound `C*(t + 2*sqrt(t)/sqrt(2*a))`.

The nonlinear parabolic iteration is now proved for bounded mild solutions.
`BUCNonlinearHigher` establishes local Lipschitz continuity of reaction
substitution, its uniform finite-order bounds on bounded state/derivative
balls, and time continuity of all derivative fields. The reaction is not
assumed globally bounded or globally Lipschitz. `HeatOrbitHigherBounds`
supplies the uniformly smoothed initial term after each restart.
`SemilinearHeatRegularity` iterates the derivative gain, using a fixed
positive restart time for continuity and fixed-length backward intervals
for bounds independent of the final horizon. It includes the cutoff case
where the initial datum need not be differentiable.

`FiniteHeatSystemRegularity` carries out the same argument for genuinely
coupled vector reactions with different positive scalar diffusion rates.
`MatrixReactionDiffusionRegularity` instantiates it with the original
diffusion's orthonormal eigenbasis, deriving positivity of every rate from
`IsSmoothParabolic`. This gives the uniform `χ • u` C⁹ bound from a
supremum bound and the original coordinate mild equations, with constants
chosen before the solution and horizon. The equations at time zero imply
all restart formulas, rather than requiring independent restart data.
The physical-space bound is connected to the split-coordinate modulation
estimates above and is used in the coupled tracking construction below.

Local solutions of the original matrix mild equations are now constructed.
`NonlinearVolterra` proves a Banach contraction on a closed continuous-path
ball, including uniqueness in that ball and a positive lifetime uniform
over bounded initial data. `FiniteHeatSystemLocalExistence` reconstructs
the real heat evolution in fixed coordinates and applies the contraction
to the original coupled reaction. `MatrixReactionDiffusionLocalExistence`
checks these coordinate identities for the orthonormal diffusion eigenbasis
and obtains local solutions with all-order positive-time spatial BUC
regularity. `HeatMildClassical` and `FiniteHeatSystemClassical` differentiate
their restarted mild equations and recover the actual pointwise PDE
`u_t = D Δu + f(u)` at every positive interior time. These proofs require
neither smooth initial data nor additional reaction hypotheses.

`BUCJointContinuity` proves the exact finite-slab continuity requirement:
compactness of a norm-continuous BUC trajectory supplies a common spatial
modulus and a uniform bound, including the initial time. `BUCSpacetimeCalculus`
assembles the time and spatial derivatives into the joint derivative.
`BUCMixedDerivatives` integrates in the closed spatial derivative graph
to prove time--space derivative commutation in BUC norm, without assuming
mixed differentiability. `ReactionDiffusionSpacetime` uses the four spatial
derivative fields to obtain joint C² regularity, including the second
time derivative. `BUCSpacetimeRegularity` keeps joint regularity of all
spatial jets, with genuine chain and product rules. `BUCSpacetimeBootstrap`
advances the joint order using the time derivative and spatial commutation;
`ReactionDiffusionSmooth` iterates this for the actual PDE to prove joint
C∞ regularity. `MatrixReactionDiffusionSpacetime` applies the result to the
constructed local solutions under the original hypotheses.

`NonlinearVolterraUniqueness` proves arbitrary-time exponential stability
and uniqueness by integral Grönwall, using Lipschitz constants only on
bounded state ranges. `FiniteHeatSystemUniqueness` reconstructs the vector
mild equation from the scalar coordinates. `MatrixReactionDiffusionUniqueness`
therefore proves uniqueness on common finite intervals under the original
parabolic hypotheses. `FiniteHeatSystemContinuation` glues compatible
solutions by the Duhamel restart identity. `FiniteHeatSystemBoundedContinuation`
restarts before a finite endpoint, using the lifetime uniform over bounded
data, and proves extension of every uniformly BUC-bounded solution on a
half-open interval. Uniqueness identifies the extension on the entire old
interval; no endpoint limit is assumed. `MatrixReactionDiffusionContinuation`
specializes this bounded-norm continuation result to the original parabolic
hypotheses and proves the extension is jointly C∞ and satisfies the PDE and
finite-slab BUC condition.

`CompatibleLocalTrajectories` constructs the compatible union of all local
solutions and takes the supremum of their lifetimes in the extended
nonnegative reals. Local extension makes each closed solution interval
strictly shorter than that supremum. `FiniteHeatSystemMaximal` verifies
these compatibility and continuation hypotheses for the coupled equations.
`EndpointNormBound` proves that a finite endpoint norm limsup gives a bound
on the entire half-open interval: first near the endpoint, then on the
remaining compact initial interval. Bounded continuation contradicts a
finite maximal lifetime, proving the paper's limsup blow-up alternative.

`MatrixReactionDiffusionLocalClassical` derives the PDE and joint smoothness
from continuity only on the actual finite slab. `MatrixReactionDiffusionMaximal`
therefore constructs a maximal classical solution under the original
parabolic hypotheses, including the initial condition, positive lifetime,
full joint C∞ regularity, and finite-endpoint blow-up alternative.
`MatrixReactionDiffusionGlobal` proves that a uniform BUC bound on this
maximal trajectory gives infinite lifetime and exactly the challenge's
`IsRDESolution` predicate. `FrontTrackingGlobal` supplies that bound using
the closed nonlinear tracking estimates, proving unconditional global
existence for the small perturbations in the challenge.

`InverseModulationCoordinates` proves that the spatial modulation shear preserves
BUC and its exact supremum norm. `FrontNonlinearity` uses the challenge's own
coordinate maps to equate the inverse-modulated norm bound with the forward
physical-space error bound in the final theorem. At zero phase and time shift,
this is exactly the original `IsCloseToFront` hypothesis.

`ModulationContinuity` proves joint continuity in translation, phase, and
BUC data, including rough data at time zero. `ModulationSpatialRegularity`
transfers time-continuous spatial jets using the actual chain rule.
`BUCSpatialRegularityLocal` glues local jets by uniqueness of derivatives,
and `MatrixReactionDiffusionPositiveJets` thereby gives all-order jets on
the whole positive-time interior without a separate physical norm bound.
`FrontPhysicalModulationRegularity` applies these results to the actual
inverse-modulated mild solution, and `RealSpatialEmbeddingRegularity`
transfers its jets to the complex full-space semigroup coordinates.

`SemigroupVariationOfConstants` differentiates the backward orbit and
integrates to obtain Duhamel's formula without generator membership at
time zero. `BUCPointwiseTimeDerivative` upgrades continuous pointwise time
derivatives to derivatives in BUC norm. `FrontClassicalDuhamel` derives
generator membership from genuine spatial jets and applies these results
to the actual front semigroup. Its hypothesis is the pointwise classical
front equation, not an assumed mild identity.

`FrontSplitClassicalDuhamel` identifies the real split-coordinate Laplacian,
drift, and reaction terms with the actual complex generator.
`FrontPhysicalModulationDifferentiability` obtains joint phase C¹ from
the forced phase equation and continuous BUC fields, and derives joint
differentiability of the actual physical inverse modulation.
`FrontPhysicalModulationPDE` establishes its exact equation on a finite
mild-solution slab; global existence of the physical solution is not assumed.
`FrontPhysicalDuhamel` combines these results to identify the actual
perturbation with the full semigroup response. `FrontPhysicalTrackingEstimate`
therefore proves the logarithmic bound for that same physical perturbation
from the source and phase bootstrap bounds, with a horizon-independent
constant. No perturbation PDE or Duhamel identity is supplied as an input.

`BUCSpatialRegularityWithin` glues spatial jets in relative time neighborhoods,
so `MatrixReactionDiffusionPositiveClosedJets` retains the right endpoint
of the positive-time slab. `InverseModulationNonlinearityContinuity` and
`FrontNonlinearityContinuity` prove BUC continuity of the source, including
rough initial data when the derivative coefficients vanish initially.
`FrontTrackingInitialZero` derives this vanishing through time `1/4` from
the actual delayed forcing and the forced Cole--Hopf equation.
`FrontPhysicalNonlinearSource` constructs genuine derivative fields and a
continuous nonlinear source from the physical mild solution and regular
phase. This local construction alone does not assert that the supplied
forcing is generated by the new source. `FrontTrackingExtension` establishes
that self-consistency using the paper's causal blockwise argument.

The transformed PDE calculation in Section 4 is now proved for classical
fields. `ModulationChainRule` derives the time and second spatial chain rules,
including the mixed `-2` term, and sums over an orthonormal basis to obtain
the gradient-square and phase-Laplacian terms. `InverseModulationPDE` derives
`eq:utildepde` and substitutes the forced phase equation to obtain
`eq:utildepde2`. Only pointwise joint time-space differentiability is needed
at the evaluation point; no smoothness at initial time is assumed.

`ModulationProfileDerivatives` proves that subtracting the stationary profile
contributes only its longitudinal derivatives and no mixed transverse term.
`FrontModulationPDE` then uses the original front ODE to derive `eq:pdev`, with
exactly `frontInverseModulationNonlinearity`, the remainder already bounded
in Lemmas 4.1 and 4.2. `CoordinateLaplacian` proves the Euclidean-to-split
Laplacian identity by tracing along the actual coordinate basis, and obtains
the split reaction--diffusion equation from the challenge's `IsRDESolution`
predicate. Thus `frontInverseModulatedPerturbation_pde_of_solution` starts
from that predicate, the inverse-modulation Ansatz, and genuine phase and
perturbation derivative data. These are equation identities, not existence
results. The coupled construction with the required BUC regularity is
provided by `FrontTrackingExistence` and `FrontTrackingGlobal`.

The delayed forcing in Section 4.2 is now constructed from a supplied
nonlinear source. `TemporalCutoff` constructs the smooth nonnegative unit-mass
cutoff supported in `[1/4,3/4]`. `DelayedHeatForcing` implements `eq:defgnew`
with the paper's positive-integer indexing, proves that its series is locally
finite, and reduces each unit time interval to its single active pulse. The
forcing on `[k,k+1]` depends only on source values in `[0,k]`, and vanishes
through time `1/4`. `DelayedHeatForcingRegularity` proves BUC-valued time
continuity and joint space-time smoothness without differentiating the source
in time: every completed block is a fixed BUC input to a positive-time heat
pulse. The cutoff removes the singularity at pulse age zero.

`DelayedHeatForcingSmoothing` proves the exact extraction of a heat factor
of age `1/8` onto the source, including interchange with the block integral.
`FrontDelayedForcing` specializes the construction to the actual `d_perp`
and adjoint pairing. It proves the initial and block supremum bounds and
combines the extraction identity with Lemma 4.2 to bound the nonlinear
forcing by the derivative-free quantity
`C * ρ(τ) * sup_r (‖v(r)‖ * (‖v(r)‖ + ‖Δσ(r)‖ + ‖∇σ(r)‖ + ‖∇σ(r)‖² + ‖g(r)‖))`
on the preceding block, expressed formally using any uniform upper bound.
The coupled blockwise existence construction is supplied separately by
`FrontTrackingExistence`. The higher-derivative forcing estimate is proved in:
`HeatHigherDerivativeBounds` distributes derivatives over positive heat
intervals, iterating the first Gaussian estimate and commuting derivatives
through the remaining heat flow. It gives a uniform bound for every
derivative through any finite order after a fixed positive heat age.
`BoundedSmoothDerivatives` uses the next derivative's bound to obtain uniform
continuity, so these are genuine BUC derivative fields.

`DelayedHeatForcingHigherDerivativeBounds` applies these estimates on the
cutoff support, proves both the direct and `1/8`-smoothed-source block bounds
at every order, and transfers polynomial time decay to all spatial derivatives.
`FrontForcingHigherDerivativeBounds` uses the original adjoint projection
and diffusivity to prove `exists_frontDelayedForcing_cn_decay`. Taking
order nine and exponent `5/4` gives `eq:gest`, with constants independent
of the source, horizon, time, and bootstrap size. No source derivative is
assumed. The transfer to the Cole--Hopf variable is now proved by the
all-order regularity and Grönwall argument described below. Quantitative
transfer to the inverse phase is proved as well. The separate physical
reaction--diffusion regularity modules supply the high-order parabolic bounds.

`DelayedHeatForcingCancellation` proves the tracking cancellation in
Step 3b of the nonlinear iteration. Each completed pulse reproduces its
preceding source block in the heat Duhamel integral. Summing the finitely
many pulses gives `eq:T3a` and the resulting recent-history formula for the
critical residual: the initial heat orbit and all older source history
cancel exactly. The remaining expression has norm at most three times any
uniform bound on the source over its last two blocks.
`DelayedPolynomialDecay` compares the current decay weight with the weight
on those recent blocks. `HeatCriticalResidualDecay` then proves that a source
bound `M*(1+t)^(-γ)` gives the critical-residual bound
`3*3^γ*M*(1+t)^(-γ)` for every `γ ≥ 0`, including the paper's `5/4`.
The initial interval is handled separately using the remaining cutoff mass.
`FrontTrackingDecay` transfers this to the actual front's adjoint projection.
Identifying the cancelled projected source with the full nonlinear
perturbation Duhamel decomposition is supplied by `FrontPhysicalDuhamel`.

The zero-order a priori argument in Lemma `lem:xiAP` is now proved for
continuous BUC-valued mild solutions. `IntegralGronwall` proves the
time-dependent integral Grönwall estimate by an integrating factor.
`ForcedColeHopfBounds` obtains `‖ξ(t)‖ ≤ B * exp (|β| * B)` from a uniform
bound `B` on the accumulated forcing norm. Integrating the paper's exact
weight `(1+t)^(-5/4)` gives mass at most four and hence the explicit bound
`‖ξ(t)‖ ≤ 4*C*exp(4*|β|*C)*M` for `0 ≤ M ≤ 1`, independently of the final
time. It also proves uniqueness of continuous mild solutions without any
smallness assumption, and derives their zero initial value from Duhamel.

The all-order spatial version of this argument is now proved as well.
`BUCSpatialRegularity` records genuine BUC derivative paths, continuous
in time, and proves their product rules. `HeatHigherRegularity` iterates
the closed first-jet argument for scalar-coefficient heat equations. At
each step, the already proved lower regularity makes the differentiated
inhomogeneous term legitimate; the next derivative is not assumed.
`DelayedHeatForcingHigherRegularity` reserves a positive heat interval
at each derivative and proves this regularity for the actual delayed
forcing, without any derivative or continuity assumption on its source.

`ForcedColeHopfHigherRegularity` gives every spatial BUC derivative of
the existing solution, including at time zero, and spatial smoothness
of the inverse phase on its small admissible range. `BUCSpatialBounds`
proves the `2^k` product bound and constructs a continuous maximum of
the genuine derivative norms. `HeatHigherDuhamelBounds` integrates a
common source majorant without derivative loss. Applying the previously
proved integrable-decay Grönwall theorem, `ForcedColeHopfHigherBounds`
obtains the explicit uniform bound
`‖ξ(t)‖_{C^k,max} ≤ 4*C*exp(4*|β|*2^k*C)*M` for `0 ≤ M ≤ 1`.
The bound predicate is proved to control the standard iterated Fréchet
derivatives, not just auxiliary fields.

`FrontForcedColeHopfHigherBounds` specializes to the original front and
adjoint projection, choosing the constant before the source, data, and
horizon. It constructs the spatially smooth transformed solution from
the unprojected source bootstrap and proves `eq:xiestC9` by taking
`k = 9`.

`ColeHopfInverseHigherBounds` transfers this estimate quantitatively to
the inverse phase. On the small range, repeated differentiation of
`S = (1 + β ξ)⁻¹` gives `DS = -β S² Dξ`; the product estimates bound
all derivatives of `S`. The identity `Dσ = S Dξ` then retains the small
factor `M`, giving `‖σ(t)‖_{C^k,max} ≤ C*M`. This works for either sign
of β, including zero. `ColeHopfInverseHigherRegularity` constructs the
corresponding time-continuous BUC derivative paths.

`FrontForcedPhaseHigherBounds` applies these results to the same classical
phase as the weighted gradient/Laplacian estimates. Its constants and
positive smallness threshold precede the horizon, source, and data.
Taking order nine gives the full `eq:sigmafullest1` estimate. A separate
theorem supplies the literal sum of the weighted norms, using a continuous
least common bound on the genuine derivatives through order nine.
Joint higher space-time regularity and physical C⁹ smoothing are supplied
by the reaction--diffusion regularity modules. The coupled bootstrap is
closed by `FrontTrackingBootstrapClosure`.

`ForcedColeHopfPhase` chooses the positive constants and smallness threshold
before the forcing and final time, ensuring `|β|*‖ξ(t)‖ ≤ 1/2`. The inverse
transform is two-Lipschitz on this range, including `β = 0` and either sign
of `β`. It gives a continuous BUC-valued phase with norm at most `2*‖ξ(t)‖`,
and the classical chain-rule calculation recovers the forced viscous
Hamilton--Jacobi equation whenever the transformed solution is classical.

Existence of the continuous mild solution is now supplied by
`ForcedColeHopfExistence`. `HeatDuhamel` proves BUC-valued continuity,
linearity, the Volterra time-factor bound, and the restart formula.
`HeatVolterra` treats a continuous time-dependent bounded coefficient:
the iterated operator has norm at most `(‖B‖*T)^n/n!`, so its Neumann
series converges on every finite horizon. This produces a unique
continuous solution without any time or coefficient smallness assumption.
Specializing to the actual multiplication coefficient `-β*g(t)` and
inhomogeneous source `-g(t)` gives the forced Cole--Hopf mild solution.
Combined with the Grönwall estimate it constructs the small continuous
phase with the uniform bound, rather than assuming a solution exists.

Restriction and uniqueness prove horizon consistency and causality under
equality of the past forcing. The mild solution obeys the exact restarted
Duhamel equation. For the actual delayed forcing from a supplied source,
it is zero through time `1/4`. The phase is unique in the class whose
Cole--Hopf transforms satisfy the mild equation.

The first spatial regularity step is now proved in
`ForcedColeHopfRegularity`: a continuous BUC first derivative of the
forcing gives a genuine first derivative of the constructed mild
solution, continuous in time in the BUC norm and satisfying the
differentiated Duhamel equation. `BUCFirstJet` proves that genuine
value/derivative pairs form a closed linear subspace invariant under
heat flow; `ScalarFirstJet` supplies the bounded product rule.
`HeatVolterraInvariant` proves that the convergent Volterra series stays
in this subspace. Uniqueness then identifies the value component with
the scalar solution already constructed. `HeatDuhamelDerivative` also
justifies differentiation of a BUC-valued heat Duhamel integral.

This applies to the actual delayed forcing, not just a supplied
derivative hypothesis: `DelayedHeatForcingDerivative` extracts the
paper's fixed `1/8` heat factor from each pulse and constructs its BUC
derivative, with norm bound and continuity through pulse boundaries.
Local finiteness gives a continuous BUC derivative of the complete
forcing without requiring spatial derivatives of its nonlinear source.
`VectorFirstJet` and `HeatLinearRegularity` extend the closed-jet argument
to vector-valued heat equations with scalar coefficients. Applying this
to the first derivative's equation proves a genuine second derivative
in `ForcedColeHopfSecondRegularity`, using only the already proved first
derivative and two derivatives of the forcing. Both spatial derivative
fields are continuous in time in the BUC norm.

`DelayedHeatForcingSecondDerivative` constructs the actual delayed
forcing's second BUC derivative by differentiating its fixed positive-time
heat datum, again requiring no derivatives of the nonlinear source. It
also proves the inverse-time second-derivative heat bound and the uniform
second-derivative pulse bound. Thus every spatial slice of the delayed
mild solution is `C²`, and its actual Laplacian is a BUC field continuous
in time. The solution and both derivative fields vanish through time
`1/4`.

Time regularity and the classical forced heat equation are now proved in
`ForcedColeHopfClassical`. `HeatDuhamelTimeRegularity` differentiates the
short-time Duhamel integral using strong heat continuity, obtains the
right time derivative from the restarted formula and the spatial heat
generator, and identifies a continuous right derivative with the full
derivative on the closed time interval. Thus the constructed solution
has a continuous BUC time-derivative field, satisfies the pointwise PDE
at interior times, and has the appropriate one-sided derivatives at the
endpoints. No derivative of the completed nonlinear source is assumed.

`ForcedPhaseClassical` applies the small-range inverse Cole--Hopf
transform to this actual classical solution. It proves spatial `C²`
regularity and the forced viscous Hamilton--Jacobi time equation for
the BUC phase, together with the existing uniform zero-order estimate.
`FrontForcedPhase` specializes this existence result to the original
`d_perp`, adjoint-projected delayed forcing, and `β = c/(2*d_perp)`;
positivity and the coefficient cancellation follow from the original
hypotheses. Both transformed solution and phase vanish through `1/4`.
The quantitative first-derivative step is now proved as well.
`HeatDuhamelBilinearBounds` gives the heat-contractivity/Grönwall estimate
in a Banach-valued BUC space, keeping the product-rule constant explicit.
`ForcedColeHopfFirstDerivativeBounds` applies it to the genuine first
jets with multiplication constant two. A `C¹` forcing bound
`C*M*(1+t)^(-5/4)` gives
`max (‖ξ(t)‖) (‖Dξ(t)‖) ≤ 4*C*exp(8*|β|*C)*M`, uniformly in the
final time for `0 ≤ M ≤ 1`. The bounded derivative is constructed and
identified with the existing mild solution, not assumed separately.

`ColeHopfInverseDerivative` constructs the BUC inverse derivative
coefficient `(1+β*ξ)^(-1)`, with norm at most two and a Lipschitz bound
on the small range. It gives a genuine BUC derivative and gradient of
the phase, both continuous in time, bounded by twice the norm of `Dξ`.
`ForcedPhaseFirstDerivativeBounds` combines this with classical phase
existence and chooses constants and a smallness threshold before the
horizon and forcing. `FrontForcedPhaseFirstDerivativeBounds` specializes
the result to the actual front coefficients and adjoint projection.

`DelayedHeatForcingFirstDerivativeBounds` identifies the actual first
derivative on each active pulse and bounds the whole `C¹` forcing norm
by the undifferentiated initial datum or completed source block, with
the fixed `1/8` heat factor. The corresponding actual-front source bound
also contains no source derivatives.

The quantitative second-order step is now proved.
`ForcedColeHopfSecondRegularity` exposes both differentiated Duhamel
equations for the genuine derivatives of the existing solution.
`ForcedColeHopfSecondDerivativeBounds` bounds their four product-rule
terms by one common C² majorant. `IntegrableDecayGronwall` then gives
`max ‖ξ(t)‖ (max ‖Dξ(t)‖ ‖D²ξ(t)‖) ≤ 4*C*exp(16*|β|*C)*M`
from the corresponding forcing decay, uniformly in the final time for
`0 ≤ M ≤ 1`. This follows the heat-contractivity and Grönwall argument
in `lem:xiAP`.

`ColeHopfInverseSecondDerivative` constructs genuine time-continuous
BUC derivative and Hessian fields for the inverse phase. Their bounds
are `2*‖Dξ‖` and `2*‖D²ξ‖ + 4*|β|*‖Dξ‖²`; tracing the Hessian gives
the actual BUC Laplacian with its bound. `ForcedPhaseSecondDerivativeBounds`
combines these with classical phase existence, choosing uniform constants
and a smallness threshold before the horizon and nonlinear source.
`DelayedHeatForcingSecondDerivativeBounds` proves the C² pulse and block
bounds from undifferentiated data using the fixed `1/8` heat age.
`FrontForcedPhaseSecondDerivativeBounds` specializes both the block estimate
and the classical phase construction to the original front and adjoint pairing.

`DelayedHeatForcingDecay` now derives the forcing's C² time-decay bound from
the undifferentiated source bound, using the initial datum on the first block
and the completed source on each later block. Its constants are independent
of the horizon and paths. `FrontTrackingDecay` specializes this to the actual
front and combines it with the classical C² phase construction. Thus the
forcing decay is no longer a separate hypothesis in that result: the inputs
are `‖v₀‖ ≤ M` and `‖N(t)‖ ≤ M*(1+t)^(-5/4)`, as at the start of `lem:key`.
This module takes a supplied source; `FrontTrackingBootstrapClosure`
discharges that assumption for the actual coupled nonlinear system.

The weighted low-order part of Step 1 is now proved as well.
`IntegrablePolynomialConvolution` proves the convolution bound with forcing
exponent `5/4` and slow exponent `0 ≤ α ≤ 5/4`, including the needed
`α = 1/2` and `α = 1`. `HeatDerivativeDecay` combines short-time
contractivity on differentiated data with long-time heat smoothing, and
integrates the resulting nonsingular estimates. The derivatives are identified
by uniqueness with the actual heat derivatives, not assumed to obey smoothing.
`ForcedColeHopfDerivativeDecay` applies these estimates to the value and
first two product-rule derivatives of `g(1+βξ)`. It obtains
`‖Dξ(t)‖ ≤ C*M*(1+t)^(-1/2)` and `‖D²ξ(t)‖ ≤ C*M*(1+t)^(-1)`
for the existing mild solution, retaining its uniform C² bound.
`ForcedPhaseDerivativeDecay` transfers both rates through the inverse
Cole--Hopf transform, including the quadratic gradient term in its Hessian,
and constructs a classical phase with time-continuous BUC gradient and
Laplacian satisfying the same rates. `FrontForcedPhaseDerivativeDecay`
specializes this to the actual diffusivity and adjoint-projected delayed
forcing, starting only from `‖v₀‖ ≤ M` and `‖N(t)‖ ≤ M*(1+t)^(-5/4)`.
Its constants and smallness threshold are chosen before the time horizon
and source. This supplies the weighted gradient/Laplacian portion of
`eq:sigmafullest1`; `FrontForcedPhaseHigherBounds` now joins it to the
C⁹ portion for the same phase. The coupled source bound is still an input.

The improved forcing estimate in Step 5 is now proved at order zero.
`LogarithmicDecayWeights` performs the power count in Lemma 4.2: the
tracking bound `K*M*log(2+t)/(1+t)` and the phase/forcing bounds give
`C*M²*(1+t)^(-3/2)*log(2+t)` for the derivative-free nonlinear expression.
`FrontSmoothedNonlinearityDecay` applies this to the actual front
nonlinearity. A continuous smoothed-source path extends the bound to time
zero, so the initial perturbation need not have spatial derivatives.
`DelayedHeatForcingImprovedDecay` transfers the smoothed-source bound
through each completed block, retaining the original initial-data pulse.
`FrontImprovedForcingDecay` combines these results into the `k = 0` case
of `eq:gbetterest`, with constants chosen before the horizon and paths.
It uses the actual delayed forcing inside the nonlinear source and derives
its preliminary `5/4` bound from the supplied source bootstrap. The inputs
are the source identity, positive-time derivative witnesses, and the
low-order phase/tracking bounds; an improved forcing bound is not assumed.
Higher-order versions of this improved estimate remain to be proved.

For the final phase comparison, `IntegrableLogarithmicDecay` proves that
the `3/2` logarithmic weight has time mass at most 32 on any nonnegative
subinterval. `ImprovedColeHopfSource` uses the improved forcing bound and
the uniform Cole--Hopf bound to prove `eq:gxibestest`, including the initial
pulse. Heat contractivity gives a uniform quadratic bound for this product's
Duhamel contribution and for the full transformed source after time one.
`ForcedColeHopfComparison` now proves the BUC Taylor estimates, the exact
initial-pulse cancellation at time one, and the restarted comparison
equation. Together with these integrable source bounds, they give
`eq:Xfullest`, with a constant independent of the time horizon and datum.
`ForcedPhaseComparison` inverts this estimate on the small Cole--Hopf range,
giving `C*(M² + M/(1+t))` for the forced/unforced phase difference. The
smallness threshold is also chosen before all paths and final times.

`FrontPhaseComparison` specializes the result to the actual diffusivity,
adjoint projection and delayed forcing, and identifies the unforced initial
datum with the challenge's prescribed initial phase. `FrontVHJComparison`
uses the actual bounded profile derivative to transfer phase control to
physical coordinates. Its conditional final estimate has exactly the
challenge's weight `C*M*(M + (1+t)⁻¹*log(2+t))` and the already constructed
classical unforced phase. `FrontTrackingVHJComparison` discharges the
tracking, Cole--Hopf, and improved forcing estimates for an actual tracking
system. `FrontTrackingGlobal` constructs the global physical solution and
its tracking systems on every finite slab, including zero initial amplitude.
`Solution.lean` combines these statements without any additional
regularity or decay assumption. Uniqueness beyond the proved mild-transform
class is not part of the challenge statement.

Lemma 4.2 is now proved under the original hypotheses. Its analytic estimate
is first established for a twice differentiable integrable weight with two
integrable derivatives. `LongitudinalPairing`
constructs the real adjoint pairing as a bounded map from joint spatial BUC
to transverse BUC and proves one and two integrations by parts on the whole
line. Integrability supplies the vanishing boundary terms; the perturbation
itself need not be integrable or decay at either end. `LongitudinalPairingDerivative`
justifies differentiation under the pairing by an integrable majorant and
constructs its transverse BUC derivative. Differentiating the first integration
by parts proves the mixed-term identity without assuming a mixed-derivative
interchange.

`HeatDivergenceSmoothing` proves that heat averaging of an actual divergence is
bounded by the undifferentiated vector-field norm times `dim(Y)/sqrt(2*b*t)`.
It also proves the scalar-vector product rule and identifies divergence of an
actual phase gradient with the challenge's Laplacian. `ProjectedNonlinearity`
then proves the exact six-term identity displayed in the paper and the uniform
bound `C*‖v‖*(‖v‖+‖Δσ‖+‖∇σ‖+‖∇σ‖²+‖g‖)`, choosing the constant before all
perturbation, phase, and forcing fields. No derivative norm of `v` remains.

`FrontProjectedNonlinearity` specializes that estimate to the actual front,
the original `d_perp`, heat time `1/8`, and genuine first and second spatial
derivative fields. The adjoint regularity prerequisite is discharged by
`FrontAdjointRegularity`, which constructs an almost-everywhere equal
representative with two integrable classical derivatives. The pairing is
proved invariant under replacing the weight almost everywhere; pointwise
smoothness of an arbitrary measurable representative is neither required nor
asserted. The final `exists_frontSmoothedNonlinearity_bound` therefore has no
extra regularity or decay hypothesis.

The weak adjoint equation and its classical regularizations are now derived
from the original spectral assumptions. `FrontAdjointEquation` embeds real BUC
test jets in the actual complex longitudinal domain, uses Fredholm solvability
to show that the real adjoint annihilates that operator, and obtains
`D ψ'' - c ψ' + f'(φ)* ψ = 0` in the weak sense. No pointwise derivative of the
supplied measurable adjoint is assumed. The adjoint reaction term is proved
integrable using the actual bounded front coefficient.

`BUCCompactSupport`, `L1Smoothing`, and `L1Mollification` construct normalized
smooth compactly supported kernels, prove differentiation under convolution,
and obtain smooth BUC approximations with two integrable derivatives. The
approximations converge to the original integrable data almost everywhere by
Lebesgue differentiation, and their L1 masses are uniformly bounded by the
original L1 mass. `FrontAdjointRegularization` applies this construction to the
original adjoint and its reaction term. It proves the exact classical equation
for each approximation, retaining the variable coefficient inside its
convolution, and uniform L1 bounds on both the adjoint and the reaction source.

`L1DerivativeInterpolation` integrates the local Taylor estimate over translated
intervals to prove `‖u'‖₁ ≤ (2/ε)‖u‖₁ + ε‖u''‖₁`. `L1EllipticEstimate` then absorbs
the drift and bounds both derivatives by the solution and source masses.
`FrontAdjointEstimates` applies this to the actual regularizations, with bounds
independent of the smoothing index. `L1DerivativeBoundedness` uses the zero
limit at infinity and the fundamental theorem of calculus to give supremum
bounds. `LipschitzAELimit` upgrades almost-everywhere convergence to pointwise
convergence to a bounded Lipschitz representative.

`ClassicalODELimit` passes from this representative to a classical two-jet:
compactness supplies a convergent subsequence of first derivatives at zero,
and the integrated ODE determines convergence at every other point. Bounded
convergence on finite intervals identifies both derivatives. Fatou transfers
the uniform L1 bounds to the limiting derivatives. `FrontAdjointRegularity`
checks the source convergence and all these hypotheses for the actual front,
proving the adjoint ODE and the integrability needed in the paper's two
integrations by parts. Exponential localization and higher adjoint smoothness
are not asserted by these results.

## Completed nonlinear assembly and verification

`FrontTrackingSystem` bundles the actual physical mild equation, forced
Cole--Hopf equation, genuine spatial jets, and self-consistent source identity.
No decay estimate or existence assertion is included in that definition.

* `FrontTrackingAPriori` combines Steps 1--5 of Lemma `key` for the same
  physical solution. It derives the physical norm bound before invoking
  parabolic C⁹ smoothing and interpolation, then improves the source to
  `C*M^(7/4)*(1+t)^(-5/4)`, including the initial cutoff interval.
* `TrackingBootstrapContinuity` proves continuity of the actual running
  supremum and the strict bootstrap improvement argument.
  `FrontTrackingInitialBound` bounds the initial source quadratically.
  `FrontTrackingBootstrapClosure` closes the bootstrap without an assumed
  source bound, and separately handles zero amplitude without dividing by zero.
* `FrontTrackingInitialSystem` constructs the initial zero-phase solution.
  `FrontDelayedForcingCausality` extends the old forcing through the next
  unit block. `FrontTrackingPhaseExtension`, `FrontTrackingSourceCongruence`,
  and `FrontTrackingExtension` construct the new phase and source and prove
  their causal self-consistency. `FrontTrackingExistence` iterates these
  steps to every finite physical slab with a horizon-independent threshold.
* `FrontTrackingGlobal` applies the closed estimates throughout the maximal
  physical lifetime. Its uniform norm bound rules out finite-time blow-up
  and yields the original global `IsRDESolution` predicate.
* `FrontTrackingVHJComparison` derives the improved quadratic forcing bound
  and applies the forced/unforced comparison, with exactly the prescribed
  initial phase and error weight. `Solution.lean` assembles the
  unchanged challenge statement, including `E_0 = 0` and `t = 0`.

`Comparator.lean` checks definitional equality of the complete
theorem types and prints the new proof's axioms. No auxiliary assumptions,
admitted lemmas, or use of the original admitted theorem enter this proof.
The original placeholder remains only because `Challenge.lean` is protected
from modification. Import the completed theorem with
`import all Solution`. The default `lake build` checks both the analytic
library and the comparator; `lake build Comparator` checks the comparator
and all of its dependencies.
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
