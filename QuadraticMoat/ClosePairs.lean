import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open scoped NumberField

/-!
# Fixed-norm pairs at finitely many nonzero differences

The algebraic part uses a field automorphism `σ` and the norm `x * σ x`.
The quadratic-extension part constructs the conjugating automorphism and
identifies the actual algebra norm using the two-element Galois group.
The final specialization applies to every quadratic number field and all
elements of its ring of integers. No discreteness, unique factorization,
or finiteness of the unit group is used.
-/

namespace QuadraticMoat

variable {K : Type*} [Field K]

/-- The norm associated to a field automorphism, with values in the ambient field. -/
def conjugateNorm (σ : K ≃+* K) (x : K) : K := x * σ x

lemma conjugateNorm_add_one (σ : K ≃+* K) (x : K) :
    conjugateNorm σ (x + 1) = conjugateNorm σ x + (x + σ x) + 1 := by
  simp only [conjugateNorm, map_add, map_one]
  ring

lemma conjugateNorm_div (σ : K ≃+* K) (x γ : K) :
    conjugateNorm σ (x / γ) = conjugateNorm σ x / conjugateNorm σ γ := by
  simp only [conjugateNorm, map_div₀]
  exact div_mul_div_comm x γ (σ x) (σ γ)

/-- Equal norms and equal norms after adding one force equality or conjugacy. -/
theorem eq_or_conjugate_of_norms (σ : K ≃+* K) {x y : K}
    (hn : conjugateNorm σ x = conjugateNorm σ y)
    (hs : conjugateNorm σ (x + 1) = conjugateNorm σ (y + 1)) :
    x = y ∨ x = σ y := by
  rw [conjugateNorm_add_one, conjugateNorm_add_one] at hs
  have ht : x + σ x = y + σ y := by
    linear_combination hs - hn
  have hp : (x - y) * (x - σ y) = 0 := by
    dsimp [conjugateNorm] at hn
    linear_combination x * ht - hn
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- For a fixed nonzero displacement there are at most two norm-fiber elements. -/
theorem eq_or_scaled_conjugate_of_norms (σ : K ≃+* K) {x y γ : K}
    (hγ : γ ≠ 0)
    (hn : conjugateNorm σ x = conjugateNorm σ y)
    (hs : conjugateNorm σ (x + γ) = conjugateNorm σ (y + γ)) :
    x = y ∨ x = γ * σ (y / γ) := by
  have hx : x / γ + 1 = (x + γ) / γ := by
    field_simp
  have hy : y / γ + 1 = (y + γ) / γ := by
    field_simp
  have hn' : conjugateNorm σ (x / γ) = conjugateNorm σ (y / γ) := by
    rw [conjugateNorm_div, conjugateNorm_div, hn]
  have hs' : conjugateNorm σ (x / γ + 1) = conjugateNorm σ (y / γ + 1) := by
    rw [hx, hy, conjugateNorm_div, conjugateNorm_div, hs]
  rcases eq_or_conjugate_of_norms σ hn' hs' with h | h
  · left
    have hm := congrArg (fun z : K => z * γ) h
    simpa [hγ] using hm
  · right
    calc
      x = σ (y / γ) * γ := (div_eq_iff hγ).mp h
      _ = γ * σ (y / γ) := mul_comm _ _

/-- A fixed pair of norm values has a finite fiber for every nonzero displacement. -/
theorem finite_fixed_norms (σ : K ≃+* K) (s t γ : K) (hγ : γ ≠ 0) :
    {x : K | conjugateNorm σ x = t ∧ conjugateNorm σ (x + γ) = s}.Finite := by
  classical
  let F : Set K := {x : K | conjugateNorm σ x = t ∧
    conjugateNorm σ (x + γ) = s}
  by_cases hF : F.Nonempty
  · obtain ⟨y, hy⟩ := hF
    apply (Set.toFinite ({y, γ * σ (y / γ)} : Set K)).subset
    intro x hx
    rcases eq_or_scaled_conjugate_of_norms σ hγ
      (hx.1.trans hy.1.symm) (hx.2.trans hy.2.symm) with h | h
    · simp [h]
    · simp [h]
  · have he : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    change F.Finite
    rw [he]
    exact Set.finite_empty

/-- Finitely many allowed norms and nonzero differences give finitely many pairs. -/
theorem finite_norm_pairs (σ : K ≃+* K) (S Δ : Set K)
    (hS : S.Finite) (hΔ : Δ.Finite) :
    {p : K × K | conjugateNorm σ p.1 ∈ S ∧ conjugateNorm σ p.2 ∈ S ∧
      p.1 - p.2 ∈ Δ ∧ p.1 ≠ p.2}.Finite := by
  classical
  let U : Set (K × K) := ⋃ t ∈ S, ⋃ s ∈ S, ⋃ γ ∈ Δ \ {0},
    (fun x : K => (x + γ, x)) ''
      {x : K | conjugateNorm σ x = t ∧ conjugateNorm σ (x + γ) = s}
  have hU : U.Finite := by
    apply hS.biUnion
    intro t ht
    apply hS.biUnion
    intro s hs
    apply hΔ.sdiff.biUnion
    intro γ hγ
    exact (finite_fixed_norms σ s t γ (by simpa using hγ.2)).image _
  apply hU.subset
  rintro ⟨a, b⟩ ⟨ha, hb, hab, hne⟩
  simp only [U, Set.mem_iUnion, exists_prop, Set.mem_image, Set.mem_ofPred_eq]
  refine ⟨conjugateNorm σ b, hb, conjugateNorm σ a, ha, a - b,
    ⟨hab, ?_⟩, b, ?_, ?_⟩
  · simpa only [Set.mem_singleton_iff, sub_eq_zero] using hne
  · constructor
    · rfl
    · simp
  · simp

end QuadraticMoat

namespace QuadraticMoat

section QuadraticExtension

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Algebra.IsQuadraticExtension F K] [Algebra.IsSeparable F K]

/-- The norm in a separable quadratic extension is the product with its conjugate. -/
theorem exists_conjugation_norm : ∃ σ : K ≃+* K,
    ∀ x : K, algebraMap F K (Algebra.norm F x) = conjugateNorm σ x := by
  classical
  have hc : Nat.card (K ≃ₐ[F] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  obtain ⟨σ, hσ, hu⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[F] K)).mp hc
  have hUniv : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, σ} := by
    ext τ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hτ : τ = 1
    · exact Or.inl hτ
    · exact Or.inr (hu τ hτ)
  refine ⟨σ.toRingEquiv, fun x => ?_⟩
  rw [Algebra.norm_eq_prod_automorphisms, hUniv, Finset.prod_pair hσ.symm]
  rfl

/-- The actual quadratic field norm has finite fixed-displacement fibers. -/
theorem finite_quadratic_fixed_norms (s t : F) (γ : K) (hγ : γ ≠ 0) :
    {x : K | Algebra.norm F x = t ∧ Algebra.norm F (x + γ) = s}.Finite := by
  obtain ⟨σ, hσ⟩ := exists_conjugation_norm (F := F) (K := K)
  apply (finite_fixed_norms σ (algebraMap F K s) (algebraMap F K t) γ hγ).subset
  intro x hx
  exact ⟨(hσ x).symm.trans (congrArg (algebraMap F K) hx.1),
    (hσ (x + γ)).symm.trans (congrArg (algebraMap F K) hx.2)⟩

/-- Finite norm sets and finite nonzero differences give finite pairs in a
separable quadratic field extension, with the actual algebra norm. -/
theorem finite_quadratic_norm_pairs (S : Set F) (Δ : Set K)
    (hS : S.Finite) (hΔ : Δ.Finite) :
    {p : K × K | Algebra.norm F p.1 ∈ S ∧ Algebra.norm F p.2 ∈ S ∧
      p.1 - p.2 ∈ Δ ∧ p.1 ≠ p.2}.Finite := by
  obtain ⟨σ, hσ⟩ := exists_conjugation_norm (F := F) (K := K)
  apply (finite_norm_pairs σ ((algebraMap F K) '' S) Δ (hS.image _) hΔ).subset
  rintro ⟨a, b⟩ ⟨ha, hb, hab, hne⟩
  exact ⟨⟨Algebra.norm F a, ha, hσ a⟩,
    ⟨Algebra.norm F b, hb, hσ b⟩, hab, hne⟩

end QuadraticExtension

/-- Number-field specialization with quadraticity expressed by degree two. -/
theorem finite_numberField_norm_pairs (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (S : Set ℚ) (Δ : Set K)
    (hS : S.Finite) (hΔ : Δ.Finite) :
    {p : K × K | Algebra.norm ℚ p.1 ∈ S ∧ Algebra.norm ℚ p.2 ∈ S ∧
      p.1 - p.2 ∈ Δ ∧ p.1 ≠ p.2}.Finite := by
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hdegree⟩
  exact finite_quadratic_norm_pairs S Δ hS hΔ

/-- The same finiteness statement for all ring-of-integer elements, including
all associates in number fields with infinite unit groups. -/
theorem finite_ringOfIntegers_norm_pairs (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (S : Set ℚ) (Δ : Set (𝓞 K))
    (hS : S.Finite) (hΔ : Δ.Finite) :
    {p : (𝓞 K) × (𝓞 K) | Algebra.norm ℚ (p.1 : K) ∈ S ∧
      Algebra.norm ℚ (p.2 : K) ∈ S ∧ p.1 - p.2 ∈ Δ ∧ p.1 ≠ p.2}.Finite := by
  let f : ((𝓞 K) × (𝓞 K)) ↪ (K × K) :=
    ⟨fun p => ((p.1 : K), (p.2 : K)), by
      intro p q h
      apply Prod.ext
      · exact NumberField.RingOfIntegers.coe_injective (congrArg Prod.fst h)
      · exact NumberField.RingOfIntegers.coe_injective (congrArg Prod.snd h)⟩
  have hf := finite_numberField_norm_pairs K hdegree S
    ((algebraMap (𝓞 K) K) '' Δ) hS (hΔ.image _)
  apply (Set.Finite.preimage_embedding f hf).subset
  rintro p ⟨h1, h2, hd, hne⟩
  refine ⟨h1, h2, ⟨p.1 - p.2, hd, ?_⟩, ?_⟩
  · exact map_sub _ _ _
  · intro h
    exact hne (NumberField.RingOfIntegers.coe_injective h)

end QuadraticMoat
