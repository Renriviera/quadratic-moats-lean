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
