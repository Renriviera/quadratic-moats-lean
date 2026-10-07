import Mathlib

/-!
The target graph uses the Euclidean norm on the full mixed Minkowski space
`ℝ^r₁ × ℂ^r₂`. All irreducibles are vertices; associates are not identified.
The theorem target below is a proposition, not an axiom or a proved theorem.
-/

namespace QuadraticMoat

open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The full Minkowski embedding of the ring of integers, with Euclidean norm. -/
noncomputable def minkowski : 𝓞 K →+ mixedEmbedding.euclidean.mixedSpace K :=
  (mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp
    ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toAddMonoidHom

theorem minkowski_injective : Function.Injective (minkowski K) :=
  (mixedEmbedding.euclidean.toMixed K).symm.injective.comp
    ((mixedEmbedding_injective K).comp (show Function.Injective (algebraMap (𝓞 K) K) from RingOfIntegers.coe_injective))

/-- Full Minkowski distance; in a real quadratic field both real embeddings occur. -/
noncomputable def minkowskiDist (a b : 𝓞 K) : ℝ :=
  dist (minkowski K a) (minkowski K b)

/-- The pullback metric along the injective full Minkowski embedding. -/
noncomputable instance minkowskiMetric : MetricSpace (𝓞 K) :=
  MetricSpace.induced (minkowski K) (minkowski_injective K) inferInstance

@[simp] theorem dist_eq_minkowskiDist (a b : 𝓞 K) :
    dist a b = minkowskiDist K a b := rfl

abbrev IrreducibleVertex := {a : 𝓞 K // Irreducible a}

noncomputable def irreducibleGraph (D : ℝ) : SimpleGraph (IrreducibleVertex K) where
  Adj a b := a ≠ b ∧ minkowskiDist K a.val b.val ≤ D
  symm := by
    constructor
    intro a b h
    exact ⟨h.1.symm, by simpa only [minkowskiDist, dist_comm] using h.2⟩
  loopless := by
    constructor
    intro a h
    exact h.1 rfl

def component (D : ℝ) (a : IrreducibleVertex K) : Set (IrreducibleVertex K) :=
  {b | (irreducibleGraph K D).Reachable a b}

/-- The requested uniform finite-component conclusion for a fixed number field. -/
def UniformEndpoint : Prop :=
  ∀ D : ℝ, ∃ B : ℕ, ∀ a : IrreducibleVertex K,
    (component K D a).Finite ∧ (component K D a).ncard ≤ B

/-- The exact unconditional target; no UFD or auxiliary prime-distribution assumption. -/
def AllQuadraticEndpoint : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → UniformEndpoint K

end QuadraticMoat
