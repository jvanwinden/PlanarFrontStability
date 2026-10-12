/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUC
public import Planarwave.Analysis.BUC2
public import Planarwave.Analysis.BUCBilinear
public import Planarwave.Analysis.BUCFDerivCoordinates
public import Planarwave.Analysis.BUCNonlinear
public import Planarwave.Analysis.BUCPartialDerivatives
public import Planarwave.Analysis.BUCOperatorConvolution
public import Planarwave.Analysis.BUCConvolutionComposition
public import Planarwave.Analysis.BUCVolterraUniqueness
public import Planarwave.Analysis.BUCSlices
public import Planarwave.Analysis.ChallengeBridge
public import Planarwave.Analysis.ClosedOperator
public import Planarwave.Analysis.ClosedOperatorFromResolvent
public import Planarwave.Analysis.ClosedOperatorResolvent
public import Planarwave.Analysis.ClosedOperatorRestriction
public import Planarwave.Analysis.ColeHopf
public import Planarwave.Analysis.ColeHopfEvolution
public import Planarwave.Analysis.ColeHopfLaplacian
public import Planarwave.Analysis.ColeHopfPDE
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
public import Planarwave.Analysis.DiagonalDiffusionSemigroup
public import Planarwave.Analysis.DiagonalHeatFourier
public import Planarwave.Analysis.DiagonalGaussianConvolution
public import Planarwave.Analysis.DiffusionSemigroup
public import Planarwave.Analysis.DiffusionGenerator
public import Planarwave.Analysis.DiffusionSmoothing
public import Planarwave.Analysis.DiffusionAnalytic
public import Planarwave.Analysis.FredholmProjection
public import Planarwave.Analysis.FrontCoefficient
public import Planarwave.Analysis.FrontNonlinearity
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
public import Planarwave.Analysis.FrontSpatialAnalytic
public import Planarwave.Analysis.FrontSpatialSemigroup
public import Planarwave.Analysis.FrontSpatialGenerator
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
public import Planarwave.Analysis.HeatEquationOneDimensional
public import Planarwave.Analysis.HeatSmoothing
public import Planarwave.Analysis.HeatSmoothingMultidimensional
public import Planarwave.Analysis.HeatSmoothMultidimensional
public import Planarwave.Analysis.HeatEquationMultidimensional
public import Planarwave.Analysis.HeatJointSmoothMultidimensional
public import Planarwave.Analysis.HolomorphicTimeExtension
public import Planarwave.Analysis.HolomorphicIntegral
public import Planarwave.Analysis.HorizontalContourShift
public import Planarwave.Analysis.LongitudinalOperator
public import Planarwave.Analysis.LongitudinalClosedness
public import Planarwave.Analysis.PhaseFunctional
public import Planarwave.Analysis.PiContourShift
public import Planarwave.Analysis.PositiveDiffusion
public import Planarwave.Analysis.ProfileProjection
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
integral, and its uniform smallness bound. This completes unforced-phase existence; the
reaction--diffusion construction and nonlinear approximation estimate remain outstanding.

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

`InverseModulationCoordinates` proves that the spatial modulation shear preserves
BUC and its exact supremum norm. `FrontNonlinearity` uses the challenge's own
coordinate maps to equate the inverse-modulated norm bound with the forward
physical-space error bound in the final theorem. At zero phase and time shift,
this is exactly the original `IsCloseToFront` hypothesis. The transformed PDE,
the smoothed nonlinear estimate of Lemma 4.2, and the forcing construction are
not asserted by these norm identities and remain to be proved.

## Milestones still needed for the challenge theorem

The phase construction is an independent prerequisite for the final comparison. Completing it
does not discharge the spectral and nonlinear stages listed above. The bounded-perturbation
theorem and all complex-frequency symbol estimates of Lemmas 2.2--2.4 are now proved.
The spatial Fourier identification and the all-time semigroup decomposition
estimate are proved as well. The next main-line targets are the smoothing and
nonlinear stages:

* Extend the proved principal spatial derivative bounds and full linearized
  analytic generation to the high spatial derivative and tame smoothing estimates
  needed by the nonlinear Duhamel argument.
* Prove the smoothed nonlinear estimate of Lemma 4.2, including the adjoint
  integration-by-parts and heat-divergence bounds; Lemma 4.1 is already proved.
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
