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
public import Planarwave.Analysis.ClosedOperatorResolvent
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
public import Planarwave.Analysis.ConvectiveHeatSmoothing
public import Planarwave.Analysis.DiagonalDiffusionSemigroup
public import Planarwave.Analysis.DiffusionSemigroup
public import Planarwave.Analysis.DiffusionGenerator
public import Planarwave.Analysis.DiffusionSmoothing
public import Planarwave.Analysis.DiffusionAnalytic
public import Planarwave.Analysis.FredholmProjection
public import Planarwave.Analysis.FrontCoefficient
public import Planarwave.Analysis.FrontEigenvalueBranch
public import Planarwave.Analysis.FrontLinearizedMild
public import Planarwave.Analysis.FrontLinearizedSemigroup
public import Planarwave.Analysis.FrontAllFrequencySemigroup
public import Planarwave.Analysis.FrontAnalyticSemigroup
public import Planarwave.Analysis.FrontCriticalSemigroup
public import Planarwave.Analysis.FrontLowFrequencyTaylor
public import Planarwave.Analysis.FrontHighFrequencySemigroup
public import Planarwave.Analysis.FrontMidFrequencySemigroup
public import Planarwave.Analysis.FrontCompactSemigroupBounds
public import Planarwave.Analysis.FrontSpectralSemigroup
public import Planarwave.Analysis.FrontLaplaceResolvent
public import Planarwave.Analysis.FrontSectorialResolvent
public import Planarwave.Analysis.FrontSpectralSeparation
public import Planarwave.Analysis.HeatSemigroup
public import Planarwave.Analysis.HeatEquationOneDimensional
public import Planarwave.Analysis.HeatSmoothing
public import Planarwave.Analysis.HeatSmoothingMultidimensional
public import Planarwave.Analysis.HeatSmoothMultidimensional
public import Planarwave.Analysis.HeatEquationMultidimensional
public import Planarwave.Analysis.HeatJointSmoothMultidimensional
public import Planarwave.Analysis.HolomorphicTimeExtension
public import Planarwave.Analysis.HolomorphicIntegral
public import Planarwave.Analysis.LongitudinalOperator
public import Planarwave.Analysis.LongitudinalClosedness
public import Planarwave.Analysis.PhaseFunctional
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
public import Planarwave.Analysis.SemigroupEigenvector
public import Planarwave.Analysis.SemigroupDuhamel
public import Planarwave.Analysis.SemigroupVolterraSeries
public import Planarwave.Analysis.SemigroupPerturbation
public import Planarwave.Analysis.SemigroupAnalyticPerturbation
public import Planarwave.Analysis.SemigroupPerturbationGenerator
public import Planarwave.Analysis.SemigroupPerturbationBound
public import Planarwave.Analysis.SemigroupPerturbationComposition
public import Planarwave.Analysis.SemigroupCompactBounds
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

The formalization of step 2 has also begun in the order used in Lemma 2.2.  The scalar
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
These are analytic-generation and invariance results, not yet spectral-gap decay estimates.

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
`κ = 2 d_perp` on one uniformly chosen contour box. This does not yet prove exponential decay
on the complementary spectral subspace, the other estimate in Lemma 2.3.
`SemigroupIntertwining` extends generator uniqueness to bounded intertwiners.
`FrontSpectralSemigroup` uses the common-domain spectral splitting to show that the critical
projection is a left eigenmap as well, commutes with the actual semigroup, and has invariant
kernel. It proves the corresponding commutation with the complementary projection on small
complex contour frequencies. These identities establish invariance, not complementary decay.

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
family still needs its decay argument on the invariant complement, followed by uniformization.

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
does not discharge the spectral and nonlinear stages listed above. The bounded-perturbation
theorem and the all-frequency estimate of Lemma 2.2 are now proved, as are the critical-mode
Taylor estimate of Lemma 2.3 and all of Lemma 2.4. The next main-line target is the
complementary low-frequency decay estimate:

* Construct the semigroup and generator on the invariant complementary spectral subspace,
  identify its spectrum and sectorial estimates, and apply the proved spectral-to-growth
  theorem and compact-family uniformization to finish the first estimate of Lemma 2.3.
  Invariance and the critical-mode Taylor estimate alone do not establish complementary decay.
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
