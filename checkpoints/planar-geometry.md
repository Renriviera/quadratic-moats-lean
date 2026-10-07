# Planar geometry checkpoint — built

Assigned module: `QuadraticMoat/PlanarGeometry.lean`.

The basis parameter is `b : Module.Basis (Fin 2) ℤ (𝓞 K)`. `coordinateGaussian b` is the linear/additive equivalence `b.equivFun.trans OAI.GaussianMoat.latticeCoords.symm`. `coordinateComplex b` is its Gaussian complex value. There is no ring-map claim about these coordinates. `scaledCoordinateComplex b scale` multiplies this value by the real scale, used with `scale ≥ 1`.

## Completed

- `coordinateStepBound b D`: 1 plus the sum of coordinate complex norms over the finite full-Minkowski D-increment ball. This is fixed independently of walk position and length, and is at least 1.
- `coordinate_dist_le_stepBound`: a full-Minkowski D-edge has coordinate distance bounded by `coordinateStepBound b D`.
- `scaled_coordinate_dist_le_stepBound`: its scaled coordinate distance is bounded by `scale * coordinateStepBound b D` for scale≥0.
- `integerWalkSegment` and `integerDifferences`: native ring-of-integers point/difference finsets.
- `coordinate_walkSegment`, `coordinate_differences`, `coordinate_differences_card`: exact transport and preservation of difference cardinalities through the additive coordinate equivalence.
- `scaled_walk_many_differences`: transports the original Gaussian rectangle/difference geometry. Given coordinate step bound D≥1 and scale≥1, supplies R,W,e,c with the scaled-coordinate rectangle, `1≤W≤R`, `norm e=1`, and
  - `n ≤ 18*(R*W)`;
  - `R*W ≤ (scale*D)^2*n^2`;
  - `R*W ≤ (scale^2 * max D (latticeBall(4*D).card)) * nativeDifferences.card`.
- `full_minkowski_walk_many_differences`: the direct full-Minkowski walk version, setting coordinate D to `coordinateStepBound b originalD`. Thus the effective scaled planar step bound is `scale * coordinateStepBound b originalD`.
- `scaled_coordinate_determinant`: scaled planar determinant equals scale² times the integer coordinate determinant.
- `coordinateGaussian_re/im`: coordinateGaussian components equal `b.repr a 0/1`.
- `coordinateComplex_norm_sq`, `scaledCoordinateComplex_norm_sq`: coordinate/scaled length squared is the corresponding coefficient-square sum, multiplied by scale². These are the interfaces needed by the independent field norm form bound.

The scaled theorem reuses the existing original `OAI.GaussianMoat.walk_many_differences`; R, W, and c are scaled, and native difference cardinality is preserved. No ring multiplication of algebraic integers is transported through the coordinate equivalence.

## Successful build

From the Lean project root:

```
./lakew build QuadraticMoat.PlanarGeometry
```

Exit 0, successful 8935 jobs. No module warnings. Lake package-local-change warnings reflect the parent's AINTLIB/ClassFieldTheory compatibility patches.

This is a geometry component, not the completed quadratic sieve. Integration must choose a scale≥1 dominating the absolute field norm form, port lattice determinant/index arguments for selected principal split factors, and integrate the sieve probability/entropy conclusion.

Successful kernel dependency audit (exit 0):

```
./lakew env lean --stdin <<'LEAN'
import QuadraticMoat.PlanarGeometry
#print axioms QuadraticMoat.coordinate_dist_le_stepBound
#print axioms QuadraticMoat.coordinate_differences_card
#print axioms QuadraticMoat.scaled_walk_many_differences
#print axioms QuadraticMoat.full_minkowski_walk_many_differences
#print axioms QuadraticMoat.scaled_coordinate_determinant
#print axioms QuadraticMoat.scaledCoordinateComplex_norm_sq
LEAN
```

All six results depend only on `[propext, Classical.choice, Quot.sound]`. No additional axioms, `sorry`, `admit`, or unsafe proof devices.
