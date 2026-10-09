# Quadratic moat formalization: bounded-support extension complete

The original irreducible-element theorem and the stronger bounded-distinct-prime-ideal-support theorem are kernel checked and exported by `QuadraticMoat`.

For every number field `K` of degree exactly two, every budget `b : ℕ`, and every `D : ℝ`, the graph of nonzero elements of `𝓞 K` whose principal ideals have at most `b` distinct prime-ideal factors has finite connected components with one cardinality bound depending on `K`, `b`, and `D`. Prime-ideal multiplicities are unrestricted; all units are included, even at budget zero. Associates are separate vertices. Edges use full Minkowski Euclidean distance, including both real embeddings for real quadratic fields. Non-UFD fields are covered without extra hypotheses. The bound is qualitative, with no explicit numerical value supplied.

New endpoints in `QuadraticMoat.BoundedFactors`:

- `bounded_distinct_factors_components_uniformly_bounded`
- `uniformEndpoint_proved`
- `finiteHitNoWalkEndpoint_proved`

The original `QuadraticMoat.irreducible_components_uniformly_bounded`, `QuadraticMoat.uniformEndpoint_proved`, and `QuadraticMoat.allQuadraticEndpoint_proved` APIs remain available.

Recorded local validation on 2026-10-09: `./lakew build` passed (10002 jobs), and `./lakew env lean checkpoints/AuditBoundedFactors.lean` passed. Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; it also checks the unit/zero edge cases. Evidence is preserved in `checkpoints/bounded-factors-validation.txt`. The original theorem's audit and build evidence remain in `checkpoints/AuditFinal.lean`, `logs/final-build.log`, and `logs/final-axioms.log`.

Read `README.md` for the exact statements, bootstrap/cache/build instructions, proof map, and pinned source attribution. Earlier checkpoints are historical; descriptions of outstanding proof work there are superseded by the completed endpoints.
