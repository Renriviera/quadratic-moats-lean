import QuadraticMoat.Model

namespace QuadraticMoat

open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

lemma minkowski_mem_lattice (a : 𝓞 K) :
    minkowski K a ∈ mixedEmbedding.euclidean.integerLattice K := by
  change (mixedEmbedding.euclidean.toMixed K) (minkowski K a) ∈
    mixedEmbedding.integerLattice K
  simp only [minkowski, AddMonoidHom.comp_apply, LinearEquiv.coe_toAddEquiv,
    AddEquiv.coe_toAddMonoidHom]
  exact ⟨a, rfl⟩

/-- Bounded full Minkowski balls contain only finitely many algebraic integers. -/
theorem finite_minkowski_ball (c : 𝓞 K) (D : ℝ) :
    {a : 𝓞 K | minkowskiDist K a c ≤ D}.Finite := by
  classical
  let L := mixedEmbedding.euclidean.integerLattice K
  have : DiscreteTopology L := by dsimp [L]; infer_instance
  have : DiscreteTopology L.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology L)
  have hc : IsClosed (L : Set (mixedEmbedding.euclidean.mixedSpace K)) :=
    L.toAddSubgroup.isClosed_of_discreteTopology
  have hf : (Metric.closedBall (minkowski K c) D ∩
      (L : Set (mixedEmbedding.euclidean.mixedSpace K))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hc
  apply (hf.preimage (minkowski_injective K).injOn).subset
  intro a ha
  exact ⟨ha, minkowski_mem_lattice K a⟩

@[simp] theorem minkowskiDist_sub_zero (a b : 𝓞 K) :
    minkowskiDist K (a - b) 0 = minkowskiDist K a b := by
  simp only [minkowskiDist, map_sub, map_zero, dist_eq_norm, sub_zero]

/-- The lattice ball count is a uniform bound, independent of its center. -/
noncomputable def neighborBound (D : ℝ) : ℕ :=
  ({a : 𝓞 K | minkowskiDist K a 0 ≤ D} : Set (𝓞 K)).ncard

/-- Every irreducible vertex has finitely many neighbors with one uniform count. -/
theorem irreducible_neighbor_bound (D : ℝ) (e : IrreducibleVertex K) :
    ((irreducibleGraph K D).neighborSet e).Finite ∧
      ((irreducibleGraph K D).neighborSet e).ncard ≤ neighborBound K D := by
  classical
  let N := (irreducibleGraph K D).neighborSet e
  let f : IrreducibleVertex K → 𝓞 K := fun b => b.val - e.val
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (sub_left_inj.mp hab)
  have hsub : f '' N ⊆ {a : 𝓞 K | minkowskiDist K a 0 ≤ D} := by
    rintro a ⟨b, hb, rfl⟩
    have hb' : minkowskiDist K e.val b.val ≤ D := hb.2
    change minkowskiDist K (b.val - e.val) 0 ≤ D
    rw [minkowskiDist_sub_zero K b.val e.val]
    simpa only [minkowskiDist, dist_comm] using hb'
  have hball := finite_minkowski_ball K 0 D
  have himage : (f '' N).Finite := hball.subset hsub
  have hN : N.Finite := (himage.preimage hf.injOn).subset (fun b hb => ⟨b, hb, rfl⟩)
  refine ⟨hN, ?_⟩
  have hcard := Set.ncard_le_ncard hsub hball
  rw [Set.InjOn.ncard_image hf.injOn] at hcard
  exact hcard

end QuadraticMoat
