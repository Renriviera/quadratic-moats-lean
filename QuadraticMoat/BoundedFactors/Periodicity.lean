import QuadraticMoat.BoundedFactors.FactorSupport

/-! Periodicity of the finite hit-budget sieve on the entire integer lattice. -/

namespace QuadraticMoat.BoundedFactors

open NumberField
open scoped Classical
variable {K : Type*} [Field K] [NumberField K]

/-- A periodic sieve must retain zero when its finite hit count fits the budget. -/
def finiteHitSieve (F : Finset (𝓞 K)) (b : ℕ) : Set (𝓞 K) :=
  {α | finiteFactorHitCount F α ≤ b}

theorem dvd_add_period_iff {f α : 𝓞 K} {Q : ℕ}
    (hf : f ∣ (Q : 𝓞 K)) (v : 𝓞 K) :
    f ∣ α + (Q : 𝓞 K) * v ↔ f ∣ α := by
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using
      dvd_sub h (dvd_mul_of_dvd_left hf v)
  · intro h
    exact dvd_add h (dvd_mul_of_dvd_left hf v)

theorem finiteFactorHitCount_add_period (F : Finset (𝓞 K)) (Q : ℕ)
    (hfactor : ∀ f ∈ F, f ∣ (Q : 𝓞 K)) (α v : 𝓞 K) :
    finiteFactorHitCount F (α + (Q : 𝓞 K) * v) = finiteFactorHitCount F α := by
  unfold finiteFactorHitCount
  congr 1
  apply Finset.filter_congr
  intro f hf
  exact dvd_add_period_iff (hfactor f hf) v

theorem finiteHitSieve_periodic (F : Finset (𝓞 K)) (b Q : ℕ)
    (hfactor : ∀ f ∈ F, f ∣ (Q : 𝓞 K)) :
    ∀ α ∈ finiteHitSieve F b, ∀ v : 𝓞 K,
      α + (Q : 𝓞 K) * v ∈ finiteHitSieve F b := by
  intro α hα v
  change finiteFactorHitCount F (α + (Q : 𝓞 K) * v) ≤ b
  rwa [finiteFactorHitCount_add_period F Q hfactor]

theorem vertex_mem_finiteHitSieve {F : Finset (𝓞 K)}
    (hprime : ∀ f ∈ F, Prime f) (hcop : (F : Set (𝓞 K)).Pairwise IsCoprime)
    {b : ℕ} (α : Vertex K b) : α.val ∈ finiteHitSieve F b :=
  (finiteFactorHitCount_le_omega hprime hcop α.property.1).trans α.property.2

/-- The bounded-factor graph injects into any containing lattice sieve. -/
def toIntegerGraph {b : ℕ} (A : Set (𝓞 K)) (D E : ℝ)
    (hDE : D ≤ E) (hA : ∀ α : Vertex K b, α.val ∈ A) :
    graph K b D →g integerLatticeGraph A E where
  toFun := Subtype.val
  map_rel' := by
    intro α β h
    exact ⟨fun heq => h.1 (Subtype.ext heq), hA α, hA β, h.2.trans hDE⟩

theorem component_bound_of_integer_bound {b : ℕ} {A : Set (𝓞 K)}
    {D E : ℝ} {M : ℕ} (hDE : D ≤ E)
    (hA : ∀ α : Vertex K b, α.val ∈ A)
    (hbound : ∀ r ∈ A, (graphComponent (integerLatticeGraph A E) r).Finite ∧
      (graphComponent (integerLatticeGraph A E) r).ncard ≤ M)
    (α : Vertex K b) :
    (component K b D α).Finite ∧ (component K b D α).ncard ≤ M := by
  classical
  let C := component K b D α
  have hsub : Subtype.val '' C ⊆ graphComponent (integerLatticeGraph A E) α.val := by
    rintro _ ⟨β, hβ, rfl⟩
    exact hβ.map (toIntegerGraph A D E hDE hA)
  have himage : (Subtype.val '' C).Finite := (hbound α.val (hA α)).1.subset hsub
  have hfin : C.Finite := (himage.preimage Subtype.val_injective.injOn).subset
    (fun β hβ => ⟨β, hβ, rfl⟩)
  refine ⟨hfin, ?_⟩
  have hcard := (Set.ncard_le_ncard hsub (hbound α.val (hA α)).1).trans
    (hbound α.val (hA α)).2
  rw [Set.InjOn.ncard_image Subtype.val_injective.injOn] at hcard
  exact hcard

theorem component_bound_of_periodic_no_walk (hdegree : Module.finrank ℚ K = 2)
    {b : ℕ} {F : Finset (𝓞 K)} {D E : ℝ} {Q : ℕ}
    (hDE : D ≤ E) (hQ : Q ≠ 0)
    (hprime : ∀ f ∈ F, Prime f) (hcop : (F : Set (𝓞 K)).Pairwise IsCoprime)
    (hfactor : ∀ f ∈ F, f ∣ (Q : 𝓞 K))
    (hno : NoInfiniteAvoidingWalk (finiteHitSieve F b) E)
    (α : Vertex K b) :
    (component K b D α).Finite ∧ (component K b D α).ncard ≤ Q ^ 2 :=
  component_bound_of_integer_bound hDE (vertex_mem_finiteHitSieve hprime hcop)
    (fun _ hr => lattice_component_bound_of_periodic_no_walk
      (quadraticCoordinates hdegree) hQ (finiteHitSieve_periodic F b Q hfactor) hno hr) α

end QuadraticMoat.BoundedFactors
