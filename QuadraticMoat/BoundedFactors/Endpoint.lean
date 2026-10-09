import QuadraticMoat.BoundedFactors.Periodicity

/-! The clean conditional bounded distinct-prime-ideal endpoint. -/

namespace QuadraticMoat.BoundedFactors

open NumberField
open scoped Classical
variable {K : Type*} [Field K] [NumberField K]

/-- The analytical finite sieve input: each nonnegative step bound and each
factor budget admit finitely many coprime prime generators with a common
integer period, whose hit-budget sieve has no infinite simple walk. -/
def FiniteHitNoWalkEndpoint (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ b : ℕ, ∀ D : ℝ, 0 ≤ D →
    ∃ (F : Finset (𝓞 K)) (Q : ℕ), Q ≠ 0 ∧
      (∀ f ∈ F, Prime f) ∧ (F : Set (𝓞 K)).Pairwise IsCoprime ∧
      (∀ f ∈ F, f ∣ (Q : 𝓞 K)) ∧
      NoInfiniteAvoidingWalk (finiteHitSieve F b) D

/-- Periodicity and factor support discharge every endpoint step after the
finite analytical hit-budget no-walk assertion. No irreducible restoration is needed. -/
theorem uniformEndpoint_of_finiteHitNoWalkEndpoint
    (hdegree : Module.finrank ℚ K = 2) (hsieve : FiniteHitNoWalkEndpoint K) :
    UniformEndpoint K := by
  intro b D
  obtain ⟨F, Q, hQ, hprime, hcop, hfactor, hno⟩ := hsieve b (max D 0) (le_max_right _ _)
  refine ⟨Q ^ 2, fun α => ?_⟩
  exact component_bound_of_periodic_no_walk hdegree (le_max_left D 0)
    hQ hprime hcop hfactor hno α

end QuadraticMoat.BoundedFactors
