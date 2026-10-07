# Native certificate checkpoint

Owned files: QuadraticMoat/BatchCertificate.lean and SieveCertificate.lean.

Current status: BatchCertificate and SieveCertificate ALL KERNEL-CHECKED.
Combined build log /private/tmp/quadratic-cert-build2.log records both
successful module builds (3.4s and 3.3s). That combined invocation exited1
only due to unrelated upstream AccurateScales, needed by factor estimates.
Native InformationTelescope also built successfully in the same invocation;
its owner subsequently independently validated its complete build.

BatchCertificate has the original numerical fields with O_K factors and
native EntropyBand/CoverageDerivation. Generic greedy finite selection,
precedingFactors, and bandScale/schedule-log helper proofs are ported.
The soundness and certificate_no_walk proofs are kernel checked against
native InformationTelescope; their APIs additionally require ctx.scale ≤ D.

SieveCertificate F hgood D uses an arbitrary PrimeFamily and a proof every
good prime has a native SplitPrime package. Its finite union sieve uses
the same global hgood choice as each dyadic batch. factor_eq_batch and
avoiding_batch are drafted to prove this compatibility. Numerical smooth
and excess fields use native planeBall cardinality. entropyBand_from_suffix
is owned by prime_supply in AccurateScales to avoid a dependency cycle.
Final soundness and the full Minkowski finite-divisor endpoint are checked.
`finiteDivisorNoWalkEndpoint_of_certificates` enlarges a full Minkowski
step bound D to ctx.scale * coordinateStepBound ctx.basis D, chooses a
certificate there, and returns its finite selected factors and period.
No-walk is inherited through scaled_coordinate_dist_le_stepBound.

Core audit `./lakew env lean /private/tmp/quadratic-certificate-core-audit.lean`
exited0. All seven endpoints, including certificate_no_walk and full
finiteDivisorNoWalkEndpoint_of_certificates, depend only on propext,
Classical.choice, Quot.sound. No sorry/custom axioms.

Also owned/checked: SeparatedFactors.lean (three enumeration/cost lemmas)
and SieveSmoothing.lean (allBins factor weight and smoothing guard), both
parameterized F,hgood and using native selectedFactors and planeBall.
Final `./lakew build QuadraticMoat.SeparatedFactors QuadraticMoat.SieveSmoothing`
exited0, 8998 jobs, each owned module compiled in3.1s. Full log
/private/tmp/quadratic-factor-build.log. All assigned certificate/factor
tasks are implemented. Final full audit
`./lakew env lean /private/tmp/quadratic-certificate-audit.lean` exited0;
all ten certificate/factor endpoints depend only on propext,
Classical.choice, Quot.sound. No sorry or custom axioms.
