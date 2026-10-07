# Final checkpoint — theorem complete

User requested a full Lean formalization of the all-quadratic moat generalization, using Astra/Sol orchestration and durable saving if subscription limits intervened. The theorem is now proved; no limits interruption occurred (latest check 3% weekly used).

Project: research/quadratic-moats/lean, isolated local Git repository.

Exact exported statement in QuadraticMoat/Main.lean:
`irreducible_components_uniformly_bounded K hdegree D` gives one B with every component finite and cardinality ≤B. Vertices are actual irreducible O_K elements, associates distinct; distance is the full Euclidean mixed Minkowski embedding, both real embeddings when applicable. Every real D is included.

Other endpoints: uniformEndpoint_proved and allQuadraticEndpoint_proved. The actual all-quadratic proof instantiates principalSplitPrimeFamily internally and constructs quadraticPlanarContext from degree two. No UFD, finite-unit, class-number, prime-supply, or sieve hypothesis remains.

Verification:
- ./lakew build QuadraticMoat passed,9988 jobs.
- ./lakew env lean checkpoints/AuditFinal.lean audits all endpoint declarations.
- Only standard propext/Classical.choice/Quot.sound; no sorryAx or added mathematical axioms.
- Two independent semantic reviews confirmed graph/metric/associates/quantifiers and absence of hidden endpoint assumptions.

All source and final logs are saved. See README.md, STATUS.md, TASKS.md. Module-specific checkpoints are historical and may mention tasks which are now complete. Original Gaussian source is retained and unmodified; original Gaussian fullMain also independently built/audited.

Environment: Lean4.34.1, pinned mathlib/CFT/AINTLIB; compatibility patches in patches/. lakew uses local project ELAN_HOME, host elan launcher. scripts/bootstrap.py reproduces pins/patches. Do not reset intentional dependency modifications. No need to reinstall on this checkout.

Implementation notes for later modifications:
- Full Minkowski metric is distinct from auxiliary plane coordinates. toPlane is additive only; CoeOut under PlanarContext works, and explicit toPlane_sub is required.
- ctx.scale≥1 makes plane norm dominate absolute field norm. Geometry at step D assumes ctx.scale≤D and uses coordinate step D/scale. Final bridge automatically enlarges any full Minkowski D to scale*coordinateStepBound.
- Native TimeLaw/ForwardKernel methods use explicit namespace application; dot notation tends to resolve original Gaussian methods because the underlying time-only types are reused.
- Original scalar bandScale/bandLength reused; native bandSize depends on native SplitSieve.
- Avoid concurrent Lake builds of overlapping dependency chains: they can race on .olean outputs. Run one authoritative final build/audit.
- CoordinateNorm's explicit real quadratic estimate avoids pathological integer typeclass search; preserve that implementation.

No outstanding formalization work. No LaTeX edits, external publication/messages, or subscription resets performed in this task.
