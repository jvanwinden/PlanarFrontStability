# Stability of planar fronts in reaction-diffusion systems

This project formalizes one of the main results from [1], following the paper's proof.

- [`Challenge.lean`](Challenge.lean) is the protected reference statement. Its original
  `sorry` remains only in the reference environment.
- [`Planarwave/Statement.lean`](Planarwave/Statement.lean) copies the reference's public
  definitions, without its main theorem. The analytic library uses these solution-side
  definitions instead of importing `Challenge`.
- [`Solution.lean`](Solution.lean) proves the public, root-level theorem
  `vHJ_approximates_planar_front`, with the same statement as the reference.
- [`comparator.json`](comparator.json) configures the built-in
  [Lean comparator](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) to compare that theorem in
  `Challenge` and `Solution`, allowing only `propext`, `Quot.sound`, and `Classical.choice`.

The reference and solution are alternative environments: **do not import both into one
Lean module**, since each defines the same statement-level constants. The `Planarwave`
library root uses only the solution-side environment. Keep the definitions in
`Planarwave/Statement.lean` synchronized with any authorized changes to `Challenge.lean`.

The project pins Lean and mathlib to `v4.35.0`. Run `lake comparator` to use Lean's
built-in comparator with `comparator.json`; its sandbox requires Linux with `bubblewrap`
installed. It builds both targets and checks their theorem statements, referenced
definitions, and proof axioms. There is no custom `Comparator.lean` module or Lake target.
An ordinary `lake build` builds the analytic library and `Solution`; it does not itself
run the comparator.

Use `import Solution` to access the public theorem. The previous
`Planarwave.vHJ_approximates_planar_front_proved` name remains a compatibility alias,
accessible with `import all Solution`. The proof's dependency map is documented in
[`Planarwave/Analysis/PaperOutline.lean`](Planarwave/Analysis/PaperOutline.lean).

[1]. B. de Rijk and J. van Winden, "Stability and dynamics of planar fronts in reaction-diffusion systems under
  nonlocalized perturbations.", arXiv.2601.05832.
