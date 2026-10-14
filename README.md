# Stability of planar fronts in reaction-diffusion systems

This project formalizes one of the main results from [1], following the paper's proof.

- [`Challenge.lean`](Challenge.lean) contains the original statement, moved to the repository
  root without changing its contents. Its original `sorry` remains as the comparison target.
- [`Solution.lean`](Solution.lean) independently proves the full statement as
  `Planarwave.vHJ_approximates_planar_front_proved`.
- [`Comparator.lean`](Comparator.lean) verifies that the two theorem types are definitionally
  equal and that the solution depends only on `propext`, `Classical.choice`, and `Quot.sound`.
  It rejects `sorryAx` and any other unexpected axiom; it does not use the challenge's admitted proof.

Run `lake build` to check the analytic library and comparator, or `lake build Comparator`
to check just the comparator and its dependencies. After building, `lake env lean Comparator.lean`
reruns the comparison and prints the solution's axioms. The original challenge's `sorry`
warning is expected; the completed solution has no such dependency.

Use `import all Solution` to access the completed theorem, since the original challenge
definitions are private Lean module declarations. The proof's dependency map is documented in
[`Planarwave/Analysis/PaperOutline.lean`](Planarwave/Analysis/PaperOutline.lean).

[1]. B. de Rijk and J. van Winden, "Stability and dynamics of planar fronts in reaction-diffusion systems under
  nonlocalized perturbations.", arXiv.2601.05832.
