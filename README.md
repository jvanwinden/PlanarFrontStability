# Stability of planar fronts in reaction-diffusion systems

This project formalizes Theorem 1.6 from [1], following the paper's proof.

The most important files are the following:
- [`Definitions.lean`](Definitions.lean) contains the definitions needed to formulate
  the theorem statement.
- [`Challenge.lean`](Challenge.lean) contains the main theorem `vHJ_approximates_planar_front_solution`,
  without proof.
- [`Solution.lean`](Solution.lean) contains the main theorem with proof, using the results in the `Planarwave`
  folder.

To audit the statement, examine `Definitions.lean` and `Challenge.lean` (note that they only import Mathlib)

To verify the proof, first run `lake exe cache get` (optional, to fetch the Mathlib cache) and then 
```
lake comparator
```
which should output `Your solution is okay!`.

The project is pinned to Lean and Mathlib version `v4.35.0`.

[1]. B. de Rijk and J. van Winden, "Stability and dynamics of planar fronts in reaction-diffusion systems under
  nonlocalized perturbations.", arXiv.2601.05832.
