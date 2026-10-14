# Stability of planar fronts in reaction-diffusion systems

This project formalizes one of the main results from [1], following the paper's proof.

- [`Challenge.lean`](Challenge.lean) is the protected reference statement. Its original
  `sorry` remains only in the reference environment.
- [`Solution.lean`](Solution.lean) copies `Challenge.lean`, adding an import of
  `Planarwave.Proof` and replacing `sorry` with the single theorem name
  `Planarwave.vHJ_approximates_planar_front_solution`, without explicit arguments.
- [`Planarwave.lean`](Planarwave.lean) is the proof library's root module, importing
  the completed proof and the analytic modules collected in the paper outline.
- [`Planarwave/Statement.lean`](Planarwave/Statement.lean) mirrors the statement definitions
  inside the `Planarwave` namespace for use by the analytic proof, avoiding collisions
  with the public declarations copied into `Solution.lean`.
- [`Planarwave/Proof.lean`](Planarwave/Proof.lean) assembles the analytic proof and transfers
  it to the copied predicates through record conversions. The comparator-facing
  theorem's default proof arguments perform these conversions in the context of
  the copied challenge hypotheses; Lean checks the resulting proof as usual.
- [`comparator.json`](comparator.json) configures the built-in
  [Lean comparator](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) to compare that theorem in
  `Challenge` and `Solution`, allowing only `propext`, `Quot.sound`, and `Classical.choice`.

The reference and solution are alternative environments: **do not import both into one
Lean module**, since each defines the same statement-level constants. The proof modules
never import `Challenge`. Keep the copied declarations in `Solution.lean` and the
namespaced mirrors in `Planarwave/Statement.lean` synchronized with any authorized
changes to `Challenge.lean`.

The project pins Lean and mathlib to `v4.35.0`. Run `lake comparator` to use Lean's
built-in comparator with `comparator.json`; its sandbox requires Linux with `bubblewrap`
installed. It builds both targets and checks their theorem statements, referenced
definitions, and proof axioms. There is no custom `Comparator.lean` module or Lake target.
The Lake file declares exactly three library targets, each with its own single
default module root and no `globs` overrides:

- `lake build Planarwave` builds the analytic proof library and its root module.
- `lake build Challenge` builds only `Challenge.lean` and its mathlib imports.
- `lake build Solution` builds `Solution.lean`, including its dependencies from
  the `Planarwave` library.

`Solution` is the only default target, so `lake build` is equivalent to building it.
Neither command runs the comparator. The `Planarwave` library never imports the
root-level `Challenge` or `Solution` modules.

Use `import Solution` to access the public theorem. The namespaced proof theorem
`Planarwave.vHJ_approximates_planar_front_proved` is available from `Planarwave.Proof`
and uses the internal predicates. The proof's dependency map is documented in
[`Planarwave/Analysis/PaperOutline.lean`](Planarwave/Analysis/PaperOutline.lean).

[1]. B. de Rijk and J. van Winden, "Stability and dynamics of planar fronts in reaction-diffusion systems under
  nonlocalized perturbations.", arXiv.2601.05832.
