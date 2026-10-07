import QuadraticMoat.ClosePairs
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Finite norm values of exceptional irreducibles

An irreducible element divisible by a specified nonunit is associated to
that nonunit, without any unique factorization assumption. Integer-valued
multiplicative norms take associates to equal values up to sign. Thus
irreducibles divisible by members of a finite selected set have finitely
many signed field norm values, even when the selected elements have
infinitely many associates.
-/

open scoped NumberField

namespace QuadraticMoat

section Monoid

variable {R : Type*} [Monoid R]

/-- An integer-valued multiplicative map changes by at most a sign on associates. -/
theorem int_map_eq_or_neg_of_associated (N : R →* ℤ) {a b : R}
    (hab : Associated a b) : N b = N a ∨ N b = -N a := by
  obtain ⟨u, hu⟩ := hab
  have hm : N a * N (u : R) = N b := by rw [← map_mul, hu]
  rcases Int.isUnit_eq_one_or (u.isUnit.map N) with h | h
  · left
    simpa [h] using hm.symm
  · right
    simpa [h] using hm.symm

/-- Every nonunit divisor of an irreducible is associated to it. -/
theorem associated_of_nonunit_dvd_irreducible {a p : R}
    (hp : Irreducible p) (ha : ¬ IsUnit a) (hd : a ∣ p) : Associated a p :=
  ((hp.dvd_iff.mp hd).resolve_left ha).symm

end Monoid

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Rational field norms of ring-of-integer associates differ only by sign. -/
theorem field_norm_eq_or_neg_of_associated {a b : 𝓞 K}
    (hab : Associated a b) :
    Algebra.norm ℚ (b : K) = Algebra.norm ℚ (a : K) ∨
      Algebra.norm ℚ (b : K) = -Algebra.norm ℚ (a : K) := by
  rcases int_map_eq_or_neg_of_associated (Algebra.norm ℤ) hab with h | h
  · left
    have hr := congrArg (fun z : ℤ => (z : ℚ)) h
    simpa only [Algebra.coe_norm_int] using hr
  · right
    have hr := congrArg (fun z : ℤ => (z : ℚ)) h
    simpa only [Int.cast_neg, Algebra.coe_norm_int] using hr

/-- The positive and negative signed field norm values of a selected set. -/
def selectedNormValues (A : Set (𝓞 K)) : Set ℚ :=
  (fun a : 𝓞 K => Algebra.norm ℚ (a : K)) '' A ∪
    (fun a : 𝓞 K => -Algebra.norm ℚ (a : K)) '' A

/-- The norm values of finitely many selected elements, up to sign, form a finite set. -/
theorem finite_selectedNormValues (A : Set (𝓞 K)) (hA : A.Finite) :
    (selectedNormValues A).Finite :=
  (hA.image _).union (hA.image _)

/-- An irreducible divisible by any selected nonunit has one of the finite selected norms. -/
theorem irreducible_norm_mem_selectedNormValues (A : Set (𝓞 K)) {p : 𝓞 K}
    (hp : Irreducible p) (hd : ∃ a ∈ A, ¬ IsUnit a ∧ a ∣ p) :
    Algebra.norm ℚ (p : K) ∈ selectedNormValues A := by
  obtain ⟨a, ha, hnu, had⟩ := hd
  rcases field_norm_eq_or_neg_of_associated
    (associated_of_nonunit_dvd_irreducible hp hnu had) with hn | hn
  · exact Or.inl ⟨a, ha, hn.symm⟩
  · exact Or.inr ⟨a, ha, hn.symm⟩

/-- The image under signed field norm of all exceptional irreducibles is finite. -/
theorem finite_norm_image_exceptional_irreducibles (A : Set (𝓞 K)) (hA : A.Finite) :
    ((fun p : 𝓞 K => Algebra.norm ℚ (p : K)) ''
      {p : 𝓞 K | Irreducible p ∧ ∃ a ∈ A, ¬ IsUnit a ∧ a ∣ p}).Finite := by
  apply (finite_selectedNormValues A hA).subset
  rintro n ⟨p, ⟨hp, hd⟩, rfl⟩
  exact irreducible_norm_mem_selectedNormValues A hp hd

/-- Ordered distinct pairs of exceptional irreducibles at finitely many
differences are finite in every quadratic number field. -/
theorem finite_exceptional_irreducible_pairs (hdegree : Module.finrank ℚ K = 2)
    (A Δ : Set (𝓞 K)) (hA : A.Finite) (hΔ : Δ.Finite) :
    {p : (𝓞 K) × (𝓞 K) | Irreducible p.1 ∧ Irreducible p.2 ∧
      (∃ a ∈ A, ¬ IsUnit a ∧ a ∣ p.1) ∧
      (∃ a ∈ A, ¬ IsUnit a ∧ a ∣ p.2) ∧ p.1 - p.2 ∈ Δ ∧ p.1 ≠ p.2}.Finite := by
  apply (finite_ringOfIntegers_norm_pairs K hdegree (selectedNormValues A) Δ
    (finite_selectedNormValues A hA) hΔ).subset
  rintro p ⟨hp1, hp2, hd1, hd2, hdiff, hne⟩
  exact ⟨irreducible_norm_mem_selectedNormValues A hp1 hd1,
    irreducible_norm_mem_selectedNormValues A hp2 hd2, hdiff, hne⟩

end NumberField

end QuadraticMoat
