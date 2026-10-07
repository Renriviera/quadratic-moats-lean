# Quadratic moat formalization checkpoint

Objective: a Lean kernel-checked unconditional theorem for every quadratic number field K, every real D, and the graph on all irreducible elements of its ring of integers, with edges at full Minkowski distance at most D: every connected component is finite and cardinalities admit one bound depending only on K and D. All associates are included. No UFD, class-number-one, or prime-supply hypothesis may remain in the final theorem.

Status: INITIALIZING. The written argument in ../quadratic-moats.tex is a research proof, not yet a Lean-verified generalization. No completion claim until the exact final statement builds and an axiom audit excludes sorryAx and additional mathematical axioms.

Scaffold: unmodified copy of the 41 GaussianMoat Lean modules from openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. Lean 4.34.1; mathlib pin d13f23b723b8a846827a245b89c10fc7d3f11612. Source license retained. The isolated project avoids unrelated original dependencies.

Plan:
1. Bootstrap pinned Lean/mathlib and build original OAI.NumberTheory.GaussianMoat.Main; audit its axioms.
2. Freeze exact number-field/irreducible/full-Minkowski theorem statement.
3. Prove quadratic fixed-norm close-pair finiteness and generic exceptional-vertex restoration.
4. Introduce arithmetic/lattice interface; port Gaussian-specific sieve geometry while reusing probability and entropy.
5. Prove quantitative principal-split prime supply from standard analytic and Hilbert class field results.
6. Instantiate every quadratic field, integrate endpoint, build, and inspect axioms.

Orchestration: parent Astra owns integration, interfaces, difficult prime supply and mathematical review; GPT-6.1 Sol agents own focused isolated modules. Agent work must record exact checked commands and residual assumptions. Definitions must not conceal the intended conclusion as hypotheses.

Resume: read this file, TASKS.md, and checkpoints/; inspect git status; run the recorded build command. Never infer success from source scans or TeX compilation. Logs and modules are saved as work proceeds. Subscription was available at initial check (0% weekly usage reported); no reset/credit action taken.
