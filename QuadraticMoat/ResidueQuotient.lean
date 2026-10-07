import QuadraticMoat.PlanarContext

namespace QuadraticMoat
open NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

noncomputable def multiples (π : 𝓞 K) : Ideal (𝓞 K) := Ideal.span ({π} : Set (𝓞 K))

@[simp] lemma mem_multiples (π z : 𝓞 K) : z ∈ multiples π ↔ π ∣ z :=
  Ideal.mem_span_singleton

lemma multiples_index (π : 𝓞 K) :
    Nat.card ((𝓞 K) ⧸ multiples π) = integerAbsNorm K π :=
  residue_card_eq_integerAbsNorm π

noncomputable def ringResidue (π z : 𝓞 K) : (𝓞 K) ⧸ multiples π :=
  Ideal.Quotient.mk (multiples π) z

@[simp] lemma ringResidue_eq (π z w : 𝓞 K) :
    ringResidue π z = ringResidue π w ↔ π ∣ z-w := by
  rw [ringResidue, ringResidue, Ideal.Quotient.eq, mem_multiples]

@[simp] lemma ringResidue_add (π z w : 𝓞 K) :
    ringResidue π (z+w) = ringResidue π z + ringResidue π w := rfl

@[simp] lemma ringResidue_sub (π z w : 𝓞 K) :
    ringResidue π (z-w) = ringResidue π z - ringResidue π w := rfl

@[simp] lemma ringResidue_zero (π : 𝓞 K) : ringResidue π 0 = 0 := rfl

instance integer_countable : Countable (𝓞 K) :=
  (RingOfIntegers.basis K).equivFun.injective.countable

instance residue_countable (π : 𝓞 K) : Countable ((𝓞 K) ⧸ multiples π) :=
  (show Function.Surjective (ringResidue π) from Ideal.Quotient.mk_surjective).countable

noncomputable def residueCode (π z : 𝓞 K) : ℕ := by
  let := Encodable.ofCountable ((𝓞 K) ⧸ multiples π)
  exact Encodable.encode (ringResidue π z)

lemma residueCode_eq (π z w : 𝓞 K) :
    residueCode π z = residueCode π w ↔ π ∣ z-w := by
  let := Encodable.ofCountable ((𝓞 K) ⧸ multiples π)
  change Encodable.encode (ringResidue π z) = Encodable.encode (ringResidue π w) ↔ _
  rw [Encodable.encode_inj, ringResidue_eq]

lemma residueCode_sub {π x y x' y' : 𝓞 K}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x-y) = residueCode π (x'-y') := by
  rw [residueCode_eq] at *
  convert dvd_sub hx hy using 1; ring

lemma residueCode_add {π x y x' y' : 𝓞 K}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x+y) = residueCode π (x'+y') := by
  rw [residueCode_eq] at *
  convert dvd_add hx hy using 1; ring

lemma finite_ringResidue {π : 𝓞 K} (hπ : π ≠ 0) : Finite ((𝓞 K) ⧸ multiples π) := by
  apply Nat.finite_of_card_ne_zero
  rw [multiples_index]
  exact (integerAbsNorm_pos hπ).ne'

lemma residueCode_range_card {π : 𝓞 K} (hπ : π ≠ 0) :
    (Set.range (residueCode π)).Finite ∧
      (Set.range (residueCode π)).ncard = integerAbsNorm K π := by
  let := finite_ringResidue hπ
  let := Encodable.ofCountable ((𝓞 K) ⧸ multiples π)
  have hs : Function.Surjective (ringResidue π) := Ideal.Quotient.mk_surjective
  have hr : Set.range (residueCode π) =
      Set.range (Encodable.encode : ((𝓞 K) ⧸ multiples π) → ℕ) := by
    change Set.range (Encodable.encode ∘ ringResidue π) = _
    rw [Set.range_comp, hs.range_eq, Set.image_univ]
  rw [hr]
  exact ⟨Set.finite_range _, by rw [Set.ncard_range_of_injective Encodable.encode_injective,
    multiples_index]⟩

/-- Prime residue classes cannot repeat inside a walk shorter than the norm radius. -/
lemma not_dvd_sub_of_plane_dist_sq_lt (P : PlanarContext K) {π z w : 𝓞 K}
    (hzw : z ≠ w) (hshort : dist (P.embed z) (P.embed w)^2 < integerAbsNorm K π) :
    ¬ π ∣ z-w := by
  intro hdiv
  have hnorm := integerAbsNorm_le_of_dvd (sub_ne_zero.mpr hzw) hdiv
  have hr : (integerAbsNorm K π : ℝ) ≤ integerAbsNorm K (z-w) := by exact_mod_cast hnorm
  have hn := P.embed_norm_bound (z-w)
  rw [map_sub P.embed, ← dist_eq_norm] at hn
  exact (not_lt_of_ge (hr.trans hn)) hshort

end QuadraticMoat
