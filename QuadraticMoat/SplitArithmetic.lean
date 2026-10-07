import QuadraticMoat.ExceptionalNorms
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.CharZero.Infinite

/-!
# Arithmetic of selected principal split primes

All statements use the native ring of integers and its integer algebra
norm. The `SplitPrime` package contains only direct algebraic splitting
data. No unique factorization of elements is assumed.
-/

open scoped NumberField
open Module

namespace QuadraticMoat

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute integer algebra norm, as a multiplicative map. -/
noncomputable def integerAbsNorm (K : Type*) [Field K] [NumberField K] : (𝓞 K) →* ℕ where
  toFun a := (Algebra.norm ℤ a).natAbs
  map_one' := by simp
  map_mul' a b := by simp [Int.natAbs_mul]

@[simp] theorem integerAbsNorm_apply (a : 𝓞 K) :
    integerAbsNorm K a = (Algebra.norm ℤ a).natAbs := rfl

@[simp] theorem integerAbsNorm_mul (a b : 𝓞 K) :
    integerAbsNorm K (a * b) = integerAbsNorm K a * integerAbsNorm K b :=
  map_mul _ _ _

@[simp] theorem integerAbsNorm_eq_zero (a : 𝓞 K) :
    integerAbsNorm K a = 0 ↔ a = 0 := by
  simp only [integerAbsNorm_apply, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff]

theorem integerAbsNorm_pos {a : 𝓞 K} (ha : a ≠ 0) :
    0 < integerAbsNorm K a := Nat.pos_of_ne_zero ((integerAbsNorm_eq_zero a).not.mpr ha)

theorem integerAbsNorm_dvd {a b : 𝓞 K} (h : a ∣ b) :
    integerAbsNorm K a ∣ integerAbsNorm K b := map_dvd (integerAbsNorm K) h

theorem integerAbsNorm_le_of_dvd {a b : 𝓞 K} (hb : b ≠ 0) (h : a ∣ b) :
    integerAbsNorm K a ≤ integerAbsNorm K b :=
  Nat.le_of_dvd (integerAbsNorm_pos hb) (integerAbsNorm_dvd h)

theorem integerAbsNorm_intCast (a : ℤ) :
    integerAbsNorm K (a : 𝓞 K) = a.natAbs ^ Module.finrank ℤ (𝓞 K) := by
  change (Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a)).natAbs = _
  rw [Algebra.norm_algebraMap, Int.natAbs_pow]

/-- This multiplicative natural norm is the absolute value of the signed field norm. -/
theorem integerAbsNorm_eq_abs_fieldNorm (a : 𝓞 K) :
    (integerAbsNorm K a : ℚ) = |Algebra.norm ℚ (a : K)| := by
  rw [integerAbsNorm_apply, Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]

theorem integerAbsNorm_eq_one_iff_isUnit (a : 𝓞 K) :
    integerAbsNorm K a = 1 ↔ IsUnit a := by
  rw [integerAbsNorm_apply, ← Ideal.absNorm_span_singleton, Ideal.absNorm_eq_one_iff]
  exact Ideal.span_singleton_eq_top

theorem product_norm_le_of_dvd {ι : Type*} (s : Finset ι) (f : ι → 𝓞 K)
    {v : 𝓞 K} (hv : v ≠ 0) (hd : (∏ i ∈ s, f i) ∣ v) :
    (∏ i ∈ s, integerAbsNorm K (f i)) ≤ integerAbsNorm K v := by
  simpa only [map_prod] using integerAbsNorm_le_of_dvd hv hd

/-- The residue quotient by an element has cardinality its absolute norm. -/
theorem residue_card_eq_integerAbsNorm (a : 𝓞 K) :
    Nat.card ((𝓞 K) ⧸ Ideal.span ({a} : Set (𝓞 K))) = integerAbsNorm K a := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  rfl

theorem prime_of_integerAbsNorm_prime {a : 𝓞 K}
    (ha : (integerAbsNorm K a).Prime) : Prime a := by
  apply Ideal.prime_of_irreducible_absNorm_span
  · intro h
    have hn : integerAbsNorm K a = 0 := (integerAbsNorm_eq_zero a).mpr h
    exact ha.ne_zero hn
  · rw [Ideal.absNorm_span_singleton]
    rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
    exact ha

/-- Direct principal splitting data at a rational prime. -/
structure SplitPrime (K : Type*) [Field K] [NumberField K] (p : ℕ) where
  prime : p.Prime
  factor : Fin 2 → 𝓞 K
  factor_norm : ∀ i, integerAbsNorm K (factor i) = p
  coprime : IsCoprime (factor 0) (factor 1)
  product_associated : Associated (factor 0 * factor 1) (p : 𝓞 K)

namespace SplitPrime

variable {p q : ℕ} (P : SplitPrime K p)

theorem factor_prime (i : Fin 2) : Prime (P.factor i) :=
  prime_of_integerAbsNorm_prime (by rw [P.factor_norm]; exact P.prime)

theorem factor_ne_zero (i : Fin 2) : P.factor i ≠ 0 := (P.factor_prime i).ne_zero

theorem factor_residue_card (i : Fin 2) :
    Nat.card ((𝓞 K) ⧸ Ideal.span ({P.factor i} : Set (𝓞 K))) = p := by
  rw [residue_card_eq_integerAbsNorm, P.factor_norm]

theorem factor_dvd_natCast (i : Fin 2) : P.factor i ∣ (p : 𝓞 K) := by
  have hp := P.product_associated.dvd
  fin_cases i
  · exact (dvd_mul_right (P.factor 0) (P.factor 1)).trans hp
  · exact (dvd_mul_left (P.factor 1) (P.factor 0)).trans hp

theorem factor_dvd_intCast_iff (i : Fin 2) (a : ℤ) :
    P.factor i ∣ (a : 𝓞 K) ↔ (p : ℤ) ∣ a := by
  constructor
  · intro hd
    have hn := integerAbsNorm_dvd hd
    rw [P.factor_norm] at hn
    rw [integerAbsNorm_intCast] at hn
    exact Int.natCast_dvd.mpr (P.prime.dvd_of_dvd_pow hn)
  · intro hd
    have hp : P.factor i ∣ ((p : ℤ) : 𝓞 K) := by simpa using P.factor_dvd_natCast i
    exact hp.trans (map_dvd (Int.castRingHom (𝓞 K)) hd)

/-- Factors lying over distinct rational primes are coprime as elements. -/
theorem factors_coprime (Q : SplitPrime K q) (hne : p ≠ q) (i j : Fin 2) :
    IsCoprime (P.factor i) (Q.factor j) := by
  have hint : IsCoprime (p : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using (Nat.coprime_primes P.prime Q.prime).mpr hne
  have hcast : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := by simpa using hint.intCast
  exact (hcast.of_isCoprime_of_dvd_left (P.factor_dvd_natCast i)).of_isCoprime_of_dvd_right
    (Q.factor_dvd_natCast j)

end SplitPrime

/-- Coordinate primitivity in a chosen integral basis. -/
def CoordinatePrimitive (b : Basis (Fin 2) ℤ (𝓞 K)) (v : 𝓞 K) : Prop :=
  IsCoprime (b.repr v 0) (b.repr v 1)

omit [NumberField K] in
theorem not_natPrime_dvd_coordinatePrimitive (b : Basis (Fin 2) ℤ (𝓞 K))
    {v : 𝓞 K} (hv : CoordinatePrimitive b v) {p : ℕ} (hp : p.Prime) :
    ¬ (p : 𝓞 K) ∣ v := by
  rintro ⟨w, hw⟩
  have hw' : v = (p : ℤ) • w := by simpa [Algebra.smul_def] using hw
  have hi : ∀ i : Fin 2, (p : ℤ) ∣ b.repr v i := by
    intro i
    refine ⟨b.repr w i, ?_⟩
    rw [hw', map_smul]
    rfl
  have hu : IsUnit (p : ℤ) := hv.isUnit_of_dvd' (hi 0) (hi 1)
  exact hp.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.mp hu)

theorem SplitPrime.not_both_dvd_coordinatePrimitive {p : ℕ} (P : SplitPrime K p)
    (b : Basis (Fin 2) ℤ (𝓞 K)) {v : 𝓞 K} (hv : CoordinatePrimitive b v) :
    ¬ (P.factor 0 ∣ v ∧ P.factor 1 ∣ v) := by
  rintro ⟨h0, h1⟩
  apply not_natPrime_dvd_coordinatePrimitive b hv P.prime
  exact P.product_associated.symm.dvd.trans (P.coprime.mul_dvd h0 h1)

/-- Choosing one factor over each of finitely many distinct rational primes,
if all chosen factors divide a nonzero element, their norm product is bounded
by that element's absolute norm. -/
theorem splitPrime_product_le_integerAbsNorm (s : Finset ℕ)
    (P : ∀ p : s, SplitPrime K p.1) (choice : s → Fin 2)
    {v : 𝓞 K} (hv : v ≠ 0) (hd : ∀ p : s, (P p).factor (choice p) ∣ v) :
    (∏ p : s, p.1) ≤ integerAbsNorm K v := by
  classical
  have hc : Pairwise (fun p q : s =>
      IsCoprime ((P p).factor (choice p)) ((P q).factor (choice q))) := by
    intro p q hpq
    exact (P p).factors_coprime (P q) (by exact fun h => hpq (Subtype.ext h)) _ _
  have hprod := Fintype.prod_dvd_of_coprime hc hd
  have hn := integerAbsNorm_le_of_dvd hv hprod
  simpa only [map_prod, SplitPrime.factor_norm] using hn

theorem splitPrime_finset_product_le_integerAbsNorm (s : Finset ℕ)
    (P : ∀ p : s, SplitPrime K p.1) (choice : s → Fin 2)
    {v : 𝓞 K} (hv : v ≠ 0) (hd : ∀ p : s, (P p).factor (choice p) ∣ v) :
    (∏ p ∈ s, p) ≤ integerAbsNorm K v := by
  have he : (∏ p : s, p.1) = ∏ p ∈ s, p := Finset.prod_coe_sort s id
  rw [← he]
  exact splitPrime_product_le_integerAbsNorm s P choice hv hd

end QuadraticMoat
