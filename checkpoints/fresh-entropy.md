# Native fresh entropy and signed residues — built and audited

Owned new modules FreshEntropy.lean, PointEnrichment.lean, SignedResidues.lean port the original native ring-dependent entropy chain, reusing the original generic FinLaw/probability lemmas. Prefix injectivity, signed prefix entropy, actual_fresh_entropy, point enrichment, difference-law fresh lower bounds, walk_fresh_lower, native ideal residue cardinalities, and signed_coverage_deficit are proved.

The geometric walk_fresh_lower takes [ctx : PlanarContext K] and adds ctx.scale≤D. Its area upper bound remains D²n², so original logD cap and constants are retained. The only modified fixed alphabet constant is ctx.scale²*max(D/ctx.scale)(original latticeBall(4*(D/ctx.scale)).card), inside hsize. Arithmetic entropy/residue APIs require no planar context.

Successful command: ./lakew build QuadraticMoat.SignedResidues (8966 jobs, exit 0). Axiom audit via ./lakew env lean --stdin importing SignedResidues and printing axioms for prefix_injective_of_no_bad, signed_prefix_entropy, actual_fresh_entropy, actual_enrichment, differenceLaw_fresh_lower, walk_fresh_lower, residue_card, signed_coverage_deficit: every theorem only propext, Classical.choice, Quot.sound. Source search finds no sorry/admit/new axiom.

Next integration is native TimeLaw/Information/schedule/package/telescope and the analytic no-infinite-walk certificate. The sieve endpoint is not yet unconditional.
