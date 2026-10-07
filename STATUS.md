# Quadratic moat formalization: complete

The unconditional all-quadratic theorem is kernel checked. `./lakew build QuadraticMoat` passed (9988 jobs), including `QuadraticMoat/Main.lean` and the exported library root. The final axiom audit reports only propext, Classical.choice, and Quot.sound.

Exact statement: for every number field K with finrank ℚ K = 2 and every real D, all connected components of the graph of irreducible elements of O_K at full Minkowski Euclidean distance ≤ D are finite, with one cardinality bound depending on K,D. Associates are separate vertices. Both real embeddings are included. No UFD or auxiliary prime-supply premise remains.

Endpoints:
- QuadraticMoat.irreducible_components_uniformly_bounded
- QuadraticMoat.uniformEndpoint_proved
- QuadraticMoat.allQuadraticEndpoint_proved

Read README.md for build instructions and the proof map. Final evidence is logs/final-build.log, logs/final-axioms.log and checkpoints/AuditFinal.lean. Earlier module checkpoints are historical; statements there about remaining work are superseded by this completed endpoint.

The isolated local Git repository preserves source, dependency pins, patches and checkpoints. Parent integration used the authorized Sol agents for arithmetic, supply, and entropy/restoration branches. Subscription was last checked at 3% weekly usage, with credits and refreshes still available; no limit interruption occurred.
