import QuadraticMoat.BoundedFactors.Main

-- Audit the mathematical statement, foundational inputs, and unconditional endpoint.
#check QuadraticMoat.BoundedFactors.omega
#check QuadraticMoat.BoundedFactors.Vertex
#check QuadraticMoat.BoundedFactors.bounded_distinct_factors_components_uniformly_bounded
#print axioms OAI.GaussianMoat.FinLaw.posterior_soft_information_lower
#print axioms QuadraticMoat.BoundedFactors.finiteFactorHitCount_le_omega
#print axioms QuadraticMoat.BoundedFactors.hitMass_sum_le
#print axioms QuadraticMoat.BoundedFactors.soft_schedule_batch_information
#print axioms QuadraticMoat.BoundedFactors.certificate_no_walk
#print axioms QuadraticMoat.BoundedFactors.finiteHitNoWalkEndpoint_proved
#print axioms QuadraticMoat.BoundedFactors.uniformEndpoint_proved
#print axioms QuadraticMoat.BoundedFactors.bounded_distinct_factors_components_uniformly_bounded

-- Semantic edge cases: zero is not a vertex; every unit fits even budget zero.
open NumberField
variable (K : Type) [Field K] [NumberField K]
example (b : ℕ) : ¬((0 : 𝓞 K) ≠ 0 ∧ QuadraticMoat.BoundedFactors.omega K 0 ≤ b) := by
  simp
example {α : 𝓞 K} (hα : IsUnit α) :
    α ≠ 0 ∧ QuadraticMoat.BoundedFactors.omega K α ≤ 0 :=
  QuadraticMoat.BoundedFactors.unit_mem_vertex K 0 hα
