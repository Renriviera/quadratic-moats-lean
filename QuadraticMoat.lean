import QuadraticMoat.Main
import QuadraticMoat.BoundedFactors.Main

/-!
Unconditional quadratic moat theorem. The graph contains every irreducible
element of the ring of integers, with full Minkowski Euclidean distance.

Main exports `irreducible_components_uniformly_bounded`,
`uniformEndpoint_proved`, and `allQuadraticEndpoint_proved`.

The `BoundedFactors` namespace additionally exports
`bounded_distinct_factors_components_uniformly_bounded`: for every natural
budget b, the graph of nonzero elements whose principal ideals have at most
b distinct prime-ideal factors has uniformly bounded finite components.
Prime-ideal multiplicities are unrestricted and units are included.
-/
