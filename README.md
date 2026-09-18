# Stability of planar fronts in reaction-diffusion systems

This project contains the statement of one of the main results from [1]. The statement is contained in 
the file `Planarwave/Challenge.lean`. The proof is in progress; that theorem still contains a
`sorry`.

The dependency plan and current milestones are documented in
[`Planarwave/Analysis/PaperOutline.lean`](Planarwave/Analysis/PaperOutline.lean).
The unforced viscous Hamilton--Jacobi phase is now constructed in every ambient dimension
`d ≥ 2`, with its prescribed initial value, full classical solution properties, and uniform
smallness bound (`Planarwave.exists_challengePhaseSolution` in
[`ChallengePhaseEvolution.lean`](Planarwave/Analysis/ChallengePhaseEvolution.lean)).
The remaining major steps are the full linear semigroup estimates, nonlinear modulation and
bootstrap, and global continuation and comparison for the reaction--diffusion solution.

Run `lake build` to check the library, including the phase construction and multidimensional
heat regularity results.

[1]. B. de Rijk and J. van Winden, "Stability and dynamics of planar fronts in reaction-diffusion systems under
  nonlocalized perturbations.", arXiv.2601.05832.
