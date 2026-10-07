# Restoration checkpoint — checked

Assigned module: `QuadraticMoat/Restoration.lean` (285 lines).

## Completed

- `baseGraph G A`: adjacency restricted to A, on the original vertex type.
- `graphComponent G x`: set of vertices reachable from x.
- `exceptionalBridge G A e f`: either one edge or two boundary edges surrounding one A-component.
- `bridgeEndpoints G A`: exceptional endpoints of bridges to distinct exceptions.
- `uniform_component_bound_of_finite_bridgeEndpoints`: finite bridge endpoints, finite degrees ≤ k, and finite base components ≤ M imply every full graph component finite and cardinality bounded by `max M ((bridgeEndpoints.ncard + 1) * (1 + k*M))`.
- `path_length_add_one_le_component_ncard`: a simple path has at most as many vertices as its finite component.
- `exceptionalBridge_dist_le`: edge distances ≤ D and base component size ≤ M imply bridge endpoint distance ≤ `(M+1)*D`, for D≥0.
- `closeExceptionalEndpoints A R`: exceptions with a distinct exceptional partner at distance ≤R.
- `uniform_component_bound_of_finite_closeExceptionalEndpoints`: the complete generic metric restoration theorem, uniform bound `max M ((closeEndpoints.ncard + 1) * (1 + k*M))`.

The last bound is slightly larger than the written proof's `max M (max 1 closeEndpoints.ncard * (1+k*M))`; it is valid and parent-approved. The proof constructs a finite saturation of F plus one exceptional root, proves it adjacency-closed, and handles components meeting no exception separately. Thus full-component finiteness is proved, never assumed.

## Exact successful commands

Run in `/Users/romainpopescu/Documents/ChatGPT/Math/research/quadratic-moats/lean`:

```
./lakew env lean QuadraticMoat/Restoration.lean
./lakew build QuadraticMoat.Restoration
```

Both exit 0. Build reported `Built QuadraticMoat.Restoration`, successful 3111 jobs.

Axiom audit command:

```
./lakew env lean --stdin <<'LEAN'
import QuadraticMoat.Restoration
#print axioms QuadraticMoat.uniform_component_bound_of_finite_bridgeEndpoints
#print axioms QuadraticMoat.exceptionalBridge_dist_le
#print axioms QuadraticMoat.uniform_component_bound_of_finite_closeExceptionalEndpoints
LEAN
```

All three depend only on `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, new mathematical axioms, `sorry`, `admit`, or unsafe proofs.

## Integration still needed

Instantiate X as the actual vertex type V (e.g. irreducible elements as a subtype), with its induced full Minkowski metric. Then the exceptional set is the complement of A inside V. Provide:

1. D≥0 and the graph edge distance bound.
2. Uniform finite base-component bound M (periodicity/sieve result).
3. Uniform finite neighbor bound k (lattice ball count).
4. Arithmetic finiteness of the close exceptional endpoint set at radius `(M+1)*D` (fixed-norm close-pair theorem and exceptional norm containment).

No metric path-length bridge remains: it is proved in this module. No arithmetic, UFD, class-number, or prime-supply assumptions enter the generic theorem. The complete quadratic-field endpoint still requires the four concrete instantiation proofs above.

## Model, lattice, and number-field reduction — checked

Additional assigned files completed: `QuadraticMoat/Model.lean`, `QuadraticMoat/Lattice.lean`, `QuadraticMoat/Reduction.lean`.

- `minkowski` is the injective additive map into `mixedEmbedding.euclidean.mixedSpace K`. `minkowskiMetric` induces the metric on the entire ring of integers from that full Euclidean embedding; irreducible vertices inherit the subtype metric.
- `AllQuadraticEndpoint` remains an explicit proposition definition, not a theorem or axiom.
- `finite_minkowski_ball` is proved for every number field using discreteness and closedness of the Euclidean integer lattice inside a proper metric space.
- `neighborBound K D` is the finite origin-ball count; `irreducible_neighbor_bound` proves a uniform finite degree bound by injecting each neighborhood through subtraction of its center.
- `finite_closeExceptionalEndpoints_of_norm_values` proves exceptional close-pair endpoint finiteness in every degree-two number field, from finite signed rational field norm values, the finite difference ball, and `finite_ringOfIntegers_norm_pairs`.
- `component_bound_of_sieve_components` is the fixed-D reduction.
- `SieveComponentEndpoint` explicitly asks only for bounded components of an avoiding subset and finite signed exceptional norm values for each D≥0. `uniformEndpoint_of_sieveComponentEndpoint` proves the exact `UniformEndpoint` from this input. Negative D is handled by a proved singleton-component theorem.
- `avoidingSelectedDivisors K T` selects irreducibles avoiding every selected nonunit divisor in T.
- `DivisorSieveComponentEndpoint` asks for a finite selected divisor set with uniformly bounded avoiding components. `uniformEndpoint_of_divisorSieveComponentEndpoint` proves the exact endpoint from this statement; finite signed exceptional norms are discharged using `ExceptionalNorms.lean`.

Successful final build:

```
./lakew build QuadraticMoat.Model QuadraticMoat.Lattice QuadraticMoat.Reduction
```

Exit 0, successful 8929 jobs, no warnings on final build. These statements are reductions. Neither `SieveComponentEndpoint K` nor `DivisorSieveComponentEndpoint K` nor `AllQuadraticEndpoint` is proved here. The remaining bridge is the actual finite-divisor sieve theorem for arbitrary quadratic number fields (including its geometry, probability/entropy, and prime supply).

Additional audit command, also exit 0:

```
./lakew env lean --stdin <<'LEAN'
import QuadraticMoat.Reduction
#print axioms QuadraticMoat.minkowski_injective
#print axioms QuadraticMoat.finite_minkowski_ball
#print axioms QuadraticMoat.irreducible_neighbor_bound
#print axioms QuadraticMoat.finite_closeExceptionalEndpoints_of_norm_values
#print axioms QuadraticMoat.uniformEndpoint_of_sieveComponentEndpoint
#print axioms QuadraticMoat.uniformEndpoint_of_divisorSieveComponentEndpoint
#print QuadraticMoat.AllQuadraticEndpoint
LEAN
```

All six theorem audits report only `[propext, Classical.choice, Quot.sound]`. Printed `AllQuadraticEndpoint` is exactly the proposition quantifying all degree-two number fields and the full `UniformEndpoint`.

## Periodicity and full reduction — checked source

Additional assigned module `QuadraticMoat/Periodicity.lean` ports the original finitely branching prefix/König argument to native ring-of-integers vertices and the full Minkowski metric.

- `infinite_component_has_walk`: an infinite avoiding component yields an injective infinite D-step walk.
- `lattice_component_finite`: the no-walk premise gives finite avoiding components.
- `quadraticCoordinates hdegree`: a degree-two number field's integral basis supplies `𝓞 K ≃+ ℤ×ℤ`, using the native ring-of-integers rank theorem.
- `periodic_component_bound`: every finite component of an avoiding set invariant under `z ↦ z + Q*v` has at most Q² vertices. Equal coordinate residues modulo Q yield a period vector; a nonzero period inside a finite component contradicts finiteness.
- `irreducible_base_bound_of_periodic_no_walk`: the induced irreducible base graph embeds into the full avoiding lattice graph, inheriting Q².
- `integerAvoidingSelectedDivisors_periodic`: selected nonunit factors dividing Q automatically make their avoiding set Q-periodic.
- `divisor_base_bound_of_no_walk`: the exact bridge from full-lattice no-walk output to the irreducible component input.
- `FiniteDivisorNoWalkEndpoint K`: the explicit remaining sieve input, for each D≥0: finite T, nonzero common-multiple period Q, selected nonunit factors divide Q, and no infinite injective D-walk avoiding T.
- `uniformEndpoint_of_finiteDivisorNoWalkEndpoint`: this explicit sieve input implies the exact `UniformEndpoint K`, for every quadratic field.

The analytic finite-sieve no-walk conclusion remains unproved. All other lattice, periodicity, exception-restoration, and finite signed norm arguments in this reduction are now proved.

Final periodicity build and audit succeeded (exit 0):

```
./lakew build QuadraticMoat.Periodicity
./lakew env lean --stdin <<'LEAN'
import QuadraticMoat.Periodicity
#print axioms QuadraticMoat.infinite_component_has_walk
#print axioms QuadraticMoat.periodic_component_bound
#print axioms QuadraticMoat.quadraticCoordinates
#print axioms QuadraticMoat.uniformEndpoint_of_finiteDivisorNoWalkEndpoint
LEAN
```

Build succeeded, 8930 jobs; no module warnings. Lake warns that AINTLIB and ClassFieldTheory packages have local compatibility patches (managed by parent). All four audited periodicity endpoints use only `[propext, Classical.choice, Quot.sound]`.
