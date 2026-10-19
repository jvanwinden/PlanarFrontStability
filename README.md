# Stability of planar fronts in reaction-diffusion systems

A Lean 4 formalization of Theorem 1.6 from [1], following the paper's proof.

The most important files are the following:
- [`Challenge.lean`](Challenge.lean) contains the necessary definitions and the main theorem `vHJ_approximates_planar_front_solution`,
  without proof.
- [`Solution.lean`](Solution.lean) contains the main theorem with proof, using the results in the `Planarwave`
  module.

To audit the theorem statement, examine `Challenge.lean` (which imports only Mathlib).

To verify the proof, first run `lake exe cache get` (optional, to fetch the Mathlib cache) and then 
```
lake comparator
```
which should output 
```
Your solution is okay!
```

The project is pinned to Lean and Mathlib version `v4.35.0`.

[1]. B. de Rijk and J. van Winden, "Stability and dynamics of planar fronts in reaction-diffusion systems under nonlocalized perturbations.", arXiv.2601.05832.
