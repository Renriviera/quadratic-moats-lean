# Resume checkpoint — active work, not a completed theorem

Read STATUS.md and TASKS.md, then module-specific checkpoints.

User explicitly authorized full Lean formalization, preferred Astra parent + GPT-6.1 Sol subagents, and asked for durable saving/graceful shutdown if subscription limits intervene. Subscription last checked at 1% weekly use; no limit issue or resets consumed.

The final intended statement is QuadraticMoat.AllQuadraticEndpoint in Model.lean. It is currently a definition, NOT a theorem. No UFD/class-number/prime-supply assumptions may remain in the final theorem.

Original Gaussian 41-module scaffold builds and fullMain axiom audit gives only standard logical axioms. Original repository remains unmodified. Isolated project here is a local Git repository.

New completed and checked chains:
- ClosePairs → ExceptionalNorms: all quadratic fields close pair finiteness and finite exceptional signed norm values.
- Model → Lattice → Restoration → Reduction → Periodicity: exact full Minkowski graph; finite balls/degree; restoration; König; Q² periodic components; exact UniformEndpoint from explicit FiniteDivisorNoWalkEndpoint remaining sieve premise.
- SplitArithmetic: native O_K norms, prime elements from prime norm, SplitPrime K p package, residue cardinal, primitive-vector at-most-one factor, product bounds; no UFD.
- PlanarGeometry → CoordinateNorm → PlanarContext: rank-two basis coordinates (additive only), finite-Minkowski-increment-to-coordinate step bound, scaled walk area/difference bound, determinant scaling, quadratic norm polynomial and norm domination by scaled plane length. Quadratic context explicitly constructed using sqrt of norm form coefficient bound.
- PrimeSupply → PrimeMoments → ZetaRegularization → PrimeIdealRegularization → HigherDegreeTail → PrimeNormSeries → FiniteFiberTransfer: original generic window-polynomial extraction, weighted Laplace moments from strong regularized limit, Euler log-tail convergence, unconditional prime-ideal regularization and higher-degree convergence, prime norm fiber reindex, coefficient transfer outside finite bad set. Arithmetic fiber count remains required.

Active agents:
- close_pairs (Sol): HilbertSplit.lean, eventual prime-norm fiber multiplicity using ordinary/small Hilbert class field. Needs exact equality count_H(p)=[H:Q] if Nonempty(SplitPrime K p), zero otherwise, away finite discriminant set. Native forward/backward splitting facts already built; CFT composition/fiber count ongoing.
- prime_supply (Sol): coefficient norm-fiber bound and finiteexception transfer; coordinates arithmetic interface with close_pairs. Analytical chain done.
- restoration (Sol): SignedSieve.lean and SignedGeometry.lean. New native SplitSieve K (finite primes + SplitPrime packets), line log/Hoeffding, commonfactor collinearity, cube proof and signed rectangle. Reuses original generic probability/Cube helpers. Parent owns PlanarContext/CoordinateNorm.
- parent: integration, reproducibility, next generic analytics port beyond signed geometry.

Critical architecture: retain original Gaussian generic entropy/probability facts through imports. Native O_K sieve needs new arithmetic and geometry. Do not globally replace GaussianInt and claim correctness. Additive coordinate map is not a ring map, especially for real fields. The scaled coordinate plane norm dominates absolute field norm; full Minkowski steps transfer by finite increment ball.

Build helper ./lakew sets local compiler. scripts/bootstrap.py reproduces dependency checkout + exact compatibility patches; patches stored locally. Original repo's AINTLIB/CFT Lean4.34.1 patches applied, dependencies pinned in manifest. Network was authorized via auto-review. Building only named CFT/AINT targets, never their default libraries.

Long-running initial CFT command may still run: ./lakew build CebotarevDensity.Density ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldPrimeSplitting (log logs/cft-analytic-baseline.log). Density built. CFT near end at this checkpoint; must audit target theorem axioms when complete.

CoordinateNorm debugging note: pure integer calc caused pathological Std.Time.Duration.instHMulInt search (44994 tries). Fixed by generic real bound, explicit calc LHS/args, and casting back to integers. This now builds. Do not undo fix.

Remaining major work: finish Hilbert norm-fiber count + unconditional rational principalSplit window supply; finish SignedGeometry; port/integrate the native finite-sieve entropy/schedule/coverage argument; use Periodicity reduction; build actual final theorem and audit it. No assumption of desired endpoint, no sorry or new axioms. Save checked milestones and checkpoint before context loss or usage stop.


## Later integration checkpoint (October 7)

CFT/AINT named baseline COMPLETED 5258/5258. Agent close_pairs notified; final HilbertSplit formula now checking. DenseBins.lean and PrimeFamily.exists_separated_parameters build with standard axiom audits.

PlaneLattice.lean and WalkWords.lean now BUILD. Key implementation detail: CoeOut (O_K) C works under [P:PlanarContext K], Coe does not synthesize K. toPlane is ONLY an additive map; simp must use toPlane_sub, never pretend ring hom. planeBall needs explicit (K:=K) when K not inferable from arguments.

SignedSieve/SignedGeometry/FreshEntropy/PointEnrichment/SignedResidues now BUILD. Native walk_fresh_lower adds hDscale : ctx.scale ≤ D and uses coordinate step D/scale; original logD geometry/displacement constants preserved. Lattice alphabet logarithm becomes log16 + log(ctx.scale² * max (D/ctx.scale) ((original latticeBall(4*(D/ctx.scale))).card)). All downstream scale margins must use this same expression.

Parent just wrote minimal native TimeLaw.lean (78 lines) and Information.lean (130 lines), reusing original TimeLaw/ForwardKernel types and generic FinLaw results. Build in progress logs/information.log, not yet claimed checked. Parent next owns MultiscaleSchedule and KernelComposition. See TASKS.md for changed agent allocations.

Still no final theorem. Next: finish native entropy/scale/telescope chain, produce finite divisor sieve no-infinite-walk from PrimeFamily, feed Periodicity reduction and audit AllQuadraticEndpoint.
