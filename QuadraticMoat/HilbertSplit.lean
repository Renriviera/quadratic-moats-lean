import QuadraticMoat.SplitArithmetic
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
import Mathlib.Data.Int.Associated
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldPrimeSplitting
import QuadraticMoat.PrimeNormSeries
import Mathlib.NumberTheory.Divisors

/-!
# Principal split ideals and element splitting packages

This module connects direct ideal-theoretic splitting data to the native
`SplitPrime` package. It also identifies principality of the fractional
ideal of a finite prime with principality of its integral ideal.
-/

open scoped NumberField Classical
open IsDedekindDomain

namespace QuadraticMoat

variable {K : Type*} [Field K] [NumberField K]

/-- Direct ideal data for a rational prime to split into two principal prime
ideals, with both residue norms equal to the rational prime. -/
def PrincipalSplitPrime (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  p.Prime ∧ ∃ v w : HeightOneSpectrum (𝓞 K), v ≠ w ∧
    v.asIdeal.IsPrincipal ∧ w.asIdeal.IsPrincipal ∧
    v.asIdeal.absNorm = p ∧ w.asIdeal.absNorm = p ∧
    v.asIdeal * w.asIdeal = Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))

/-- Generators of two distinct principal prime ideals with the expected
norms and product form an element splitting package. -/
theorem splitPrime_of_principalSplitPrime {p : ℕ} (hp : PrincipalSplitPrime K p) :
    Nonempty (SplitPrime K p) := by
  classical
  obtain ⟨hp, v, w, hne, hv, hw, hvn, hwn, hprod⟩ := hp
  let := hv
  let := hw
  let a := Submodule.IsPrincipal.generator v.asIdeal
  let b := Submodule.IsPrincipal.generator w.asIdeal
  have ha : Ideal.span ({a} : Set (𝓞 K)) = v.asIdeal := Ideal.span_singleton_generator _
  have hb : Ideal.span ({b} : Set (𝓞 K)) = w.asIdeal := Ideal.span_singleton_generator _
  have hcop : IsCoprime a b := by
    apply (Ideal.isCoprime_span_singleton_iff a b).mp
    rw [ha, hb, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance
      (by intro he; apply hne; exact HeightOneSpectrum.ext he)
  have hnorma : integerAbsNorm K a = p := by
    rw [integerAbsNorm_apply, ← Ideal.absNorm_span_singleton, ha, hvn]
  have hnormb : integerAbsNorm K b = p := by
    rw [integerAbsNorm_apply, ← Ideal.absNorm_span_singleton, hb, hwn]
  have hassoc : Associated (a * b) (p : 𝓞 K) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    rw [← Ideal.span_singleton_mul_span_singleton, ha, hb, hprod]
  refine ⟨⟨hp, ![a, b], ?_, ?_, ?_⟩⟩
  · intro i
    fin_cases i
    · exact hnorma
    · exact hnormb
  · exact hcop
  · exact hassoc

/-- Element splitting data produces two distinct principal prime ideals. -/
theorem principalSplitPrime_of_splitPrime {p : ℕ} (P : SplitPrime K p) :
    PrincipalSplitPrime K p := by
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨Ideal.span {P.factor 0}, (Ideal.span_singleton_prime (P.factor_ne_zero 0)).mpr
      (P.factor_prime 0), by simpa using P.factor_ne_zero 0⟩
  let w : HeightOneSpectrum (𝓞 K) :=
    ⟨Ideal.span {P.factor 1}, (Ideal.span_singleton_prime (P.factor_ne_zero 1)).mpr
      (P.factor_prime 1), by simpa using P.factor_ne_zero 1⟩
  refine ⟨P.prime, v, w, ?_, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro he
    have hid : Ideal.span ({P.factor 0} : Set (𝓞 K)) = Ideal.span {P.factor 1} :=
      congrArg HeightOneSpectrum.asIdeal he
    have hc : IsCoprime (Ideal.span ({P.factor 0} : Set (𝓞 K)))
      (Ideal.span ({P.factor 1} : Set (𝓞 K))) :=
      (Ideal.isCoprime_span_singleton_iff _ _).mpr P.coprime
    rw [hid] at hc
    have htop : Ideal.span ({P.factor 1} : Set (𝓞 K)) = ⊤ :=
      Ideal.isUnit_iff.mp (isCoprime_self.mp hc)
    exact (P.factor_prime 1).not_isUnit (Ideal.span_singleton_eq_top.mp htop)
  · exact (Ideal.absNorm_span_singleton _).trans (P.factor_norm 0)
  · exact (Ideal.absNorm_span_singleton _).trans (P.factor_norm 1)
  · exact (Ideal.span_singleton_mul_span_singleton _ _).trans
      (Ideal.span_singleton_eq_span_singleton.mpr P.product_associated)

theorem principalSplitPrime_iff_splitPrime (p : ℕ) :
    PrincipalSplitPrime K p ↔ Nonempty (SplitPrime K p) :=
  ⟨splitPrime_of_principalSplitPrime, fun ⟨P⟩ => principalSplitPrime_of_splitPrime P⟩

/-- A rational prime away from the discriminant has squarefree extended ideal. -/
theorem squarefree_natPrime_ideal_of_not_dvd_discr {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K) :
    Squarefree (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) := by
  classical
  let I : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K)}
  have hI0 : I ≠ 0 := by
    change Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥
    exact Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hp.ne_zero)
  apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mpr
  rw [Multiset.nodup_iff_count_le_one]
  intro Q
  by_cases hQ : Q ∈ UniqueFactorizationMonoid.normalizedFactors I
  · have hprime : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    let : Q.IsPrime := Ideal.isPrime_of_prime hprime
    have hd : I ≤ Q := Ideal.dvd_iff_le.mp
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ)
    have hmem : (p : 𝓞 K) ∈ Q := hd (Ideal.mem_span_singleton_self _)
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    let : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
      (Ideal.liesOver_span_iff (Ideal.isPrime_of_prime hprime).ne_top hpi).mpr (by simpa using hmem)
    let : Algebra.IsUnramifiedAt ℤ Q :=
      (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpi).mp hdisc Q inferInstance (by simpa using hmem)
    have he : Q.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    have hmap : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) = I := by
      simp [I, Ideal.map_span]
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (Ideal.span ({(p : ℤ)} : Set ℤ)) Q (by rw [hmap]; exact hI0), hmap] at he
    exact he.le
  · simp only [Multiset.count_eq_zero.mpr hQ, zero_le]

/-- In a quadratic field, a principal degree-one prime over an unramified
rational prime supplies both principal splitting factors. Unramifiedness
is expressed here as squarefreeness of the rational prime ideal. -/
theorem splitPrime_of_norm_prime_of_squarefree
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hsq : Squarefree (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    {a : 𝓞 K} (ha : integerAbsNorm K a = p) : Nonempty (SplitPrime K p) := by
  classical
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hdegree⟩
  obtain ⟨σ, hσ⟩ := exists_conjugation_norm (F := ℚ) (K := K)
  let b : 𝓞 K := NumberField.RingOfIntegers.mapRingEquiv σ a
  have hprodK : (a : K) * σ (a : K) = (Algebra.norm ℤ a : K) := by
    change conjugateNorm σ (a : K) = _
    rw [← hσ, ← Algebra.coe_norm_int]
    simp
  have hprod : a * b = (Algebra.norm ℤ a : 𝓞 K) := by
    apply NumberField.RingOfIntegers.coe_injective
    simpa only [map_mul, b, NumberField.RingOfIntegers.mapRingEquiv_apply, map_intCast] using hprodK
  have hint : Associated (Algebra.norm ℤ a) (p : ℤ) :=
    Int.natAbs_eq_iff_associated.mp (by simpa using ha)
  have hassoc : Associated (a * b) (p : 𝓞 K) := by
    apply (Associated.of_eq hprod).trans
    simpa using hint.map (Int.castRingHom (𝓞 K))
  have hnprod : integerAbsNorm K (a * b) = integerAbsNorm K (p : 𝓞 K) :=
    associated_iff_eq.mp (hassoc.map (integerAbsNorm K))
  have hb : integerAbsNorm K b = p := by
    apply Nat.mul_left_cancel hp.pos
    have hpn : integerAbsNorm K (p : 𝓞 K) = p * p := by
      simp [integerAbsNorm, Algebra.norm_natCast, NumberField.RingOfIntegers.rank,
        hdegree, pow_two, Int.natAbs_mul]
    rw [integerAbsNorm_mul, ha, hpn] at hnprod
    exact hnprod
  have hIa : (Ideal.span ({a} : Set (𝓞 K))).IsPrime :=
    (Ideal.span_singleton_prime (prime_of_integerAbsNorm_prime (ha ▸ hp)).ne_zero).mpr
      (prime_of_integerAbsNorm_prime (ha ▸ hp))
  have hIb : (Ideal.span ({b} : Set (𝓞 K))).IsPrime :=
    (Ideal.span_singleton_prime (prime_of_integerAbsNorm_prime (hb ▸ hp)).ne_zero).mpr
      (prime_of_integerAbsNorm_prime (hb ▸ hp))
  have hIa0 : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊥ := by
    simpa using (prime_of_integerAbsNorm_prime (ha ▸ hp)).ne_zero
  have hIb0 : Ideal.span ({b} : Set (𝓞 K)) ≠ ⊥ := by
    simpa using (prime_of_integerAbsNorm_prime (hb ▸ hp)).ne_zero
  have hidealprod : Ideal.span ({a} : Set (𝓞 K)) * Ideal.span {b} =
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) :=
    (Ideal.span_singleton_mul_span_singleton _ _).trans
      (Ideal.span_singleton_eq_span_singleton.mpr hassoc)
  have hne : Ideal.span ({a} : Set (𝓞 K)) ≠ Ideal.span {b} := by
    intro he
    have hu : IsUnit (Ideal.span ({a} : Set (𝓞 K))) := hsq _ (by
      rw [← hidealprod, ← he])
    have hau : IsUnit a := Ideal.span_singleton_eq_top.mp (Ideal.isUnit_iff.mp hu)
    exact hp.ne_one (ha.symm.trans ((integerAbsNorm_eq_one_iff_isUnit a).mpr hau))
  have hcop : IsCoprime a b := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [Ideal.isCoprime_iff_sup_eq]
    exact (hIa.isMaximal hIa0).coprime_of_ne (hIb.isMaximal hIb0) hne
  refine ⟨⟨hp, ![a, b], ?_, hcop, hassoc⟩⟩
  intro i
  fin_cases i
  · exact ha
  · exact hb

/-- A principal prime ideal of norm p over an unramified rational p gives
the native element splitting package. -/
theorem splitPrime_of_principal_prime_norm
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hsq : Squarefree (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal.IsPrincipal)
    (hn : v.asIdeal.absNorm = p) : Nonempty (SplitPrime K p) := by
  let := hv
  apply splitPrime_of_norm_prime_of_squarefree hdegree hp hsq
    (a := Submodule.IsPrincipal.generator v.asIdeal)
  rw [integerAbsNorm_apply, ← Ideal.absNorm_span_singleton, Ideal.span_singleton_generator, hn]

theorem splitPrime_of_principal_prime_norm_of_not_dvd_discr
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal.IsPrincipal)
    (hn : v.asIdeal.absNorm = p) : Nonempty (SplitPrime K p) :=
  splitPrime_of_principal_prime_norm hdegree hp
    (squarefree_natPrime_ideal_of_not_dvd_discr hp hdisc) v hv hn

theorem splitPrime_iff_exists_principal_prime_norm
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K) :
    Nonempty (SplitPrime K p) ↔ ∃ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal.IsPrincipal ∧ v.asIdeal.absNorm = p := by
  constructor
  · rintro ⟨P⟩
    obtain ⟨_, v, w, _, hv, _, hn, _⟩ := principalSplitPrime_of_splitPrime P
    exact ⟨v, hv, hn⟩
  · rintro ⟨v, hv, hn⟩
    exact splitPrime_of_principal_prime_norm_of_not_dvd_discr hdegree hp hdisc v hv hn

/-- Every prime ideal of norm p is principal once the principal splitting
package at p exists. -/
theorem prime_norm_isPrincipal_of_splitPrime {p : ℕ} (P : SplitPrime K p)
    (v : HeightOneSpectrum (𝓞 K)) (hn : v.asIdeal.absNorm = p) :
    v.asIdeal.IsPrincipal := by
  obtain ⟨_, v0, v1, _, hv0, hv1, _, _, hprod⟩ := principalSplitPrime_of_splitPrime P
  have hmem : (p : 𝓞 K) ∈ v.asIdeal := by rw [← hn]; exact v.asIdeal.absNorm_mem
  have hd : v.asIdeal ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem))
  rw [← hprod] at hd
  rcases v.prime.dvd_or_dvd hd with h | h
  · have he : v0.asIdeal = v.asIdeal :=
      Ideal.IsMaximal.eq_of_le inferInstance v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)
    exact he ▸ hv0
  · have he : v1.asIdeal = v.asIdeal :=
      Ideal.IsMaximal.eq_of_le inferInstance v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)
    exact he ▸ hv1

/-- Exactly two prime ideals have norm p when the element splitting package exists. -/
theorem card_prime_norm_fiber_of_splitPrime {p : ℕ} (P : SplitPrime K p) :
    Nat.card {v : HeightOneSpectrum (𝓞 K) // v.asIdeal.absNorm = p} = 2 := by
  classical
  obtain ⟨_, v0, v1, hne, _, _, hn0, hn1, hprod⟩ := principalSplitPrime_of_splitPrime P
  have he : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal.absNorm = p} = {v0, v1} := by
    ext v
    constructor
    · intro hn
      have hmem : (p : 𝓞 K) ∈ v.asIdeal := by rw [← hn]; exact v.asIdeal.absNorm_mem
      have hd : v.asIdeal ∣ v0.asIdeal * v1.asIdeal := by
        rw [hprod]
        exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem))
      rcases v.prime.dvd_or_dvd hd with h | h
      · have hi : v0.asIdeal = v.asIdeal :=
          Ideal.IsMaximal.eq_of_le inferInstance v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)
        exact Or.inl (HeightOneSpectrum.ext hi.symm)
      · have hi : v1.asIdeal = v.asIdeal :=
          Ideal.IsMaximal.eq_of_le inferInstance v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)
        exact Or.inr (HeightOneSpectrum.ext hi.symm)
    · rintro (rfl | rfl)
      · exact hn0
      · exact hn1
  change Nat.card {v : HeightOneSpectrum (𝓞 K) | v.asIdeal.absNorm = p} = 2
  rw [he, Nat.card_coe_set_eq]
  exact Set.ncard_pair hne

/-- Absolute degree-one primes stay degree one when contracted to an
intermediate number field, and their relative inertia degree is one. -/
theorem prime_norm_under_and_inertiaDeg
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 L))
    (hn : w.asIdeal.absNorm = p) :
    (w.under (𝓞 K)).asIdeal.absNorm = p ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have hpow := Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 K)).asIdeal w.asIdeal
  exact hp.pow_eq_iff.mp (hpow.trans hn)

/-- In an everywhere finitely unramified Galois extension, an absolute
degree-one prime forces complete splitting of its contracted finite prime. -/
theorem prime_norm_splits_completely_of_unramified
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hU : ClassFieldTheory.IsUnramifiedAtFinitePlaces K L)
    {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 L))
    (hn : w.asIdeal.absNorm = p) :
    ClassFieldTheory.FinitePrimeSplitsCompletely K L (w.under (𝓞 K)) := by
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let v := w.under (𝓞 K)
  let : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hwf : w.asIdeal.inertiaDeg (𝓞 K) = 1 :=
    (prime_norm_under_and_inertiaDeg L hp w hn).2
  intro w' hw'
  let : w'.asIdeal.LiesOver v.asIdeal := hw'
  refine ⟨(hU v).ramificationIdx_eq_one hw', ?_⟩
  exact (Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal
    (L ≃ₐ[K] L)).trans hwf

/-- Nonzero prime ideals above a fixed finite prime, in either native presentation. -/
noncomputable def heightPrimesOverEquiv
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} ≃
      v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.2⟩, Q.2.2⟩
  left_inv w := by apply Subtype.ext; apply HeightOneSpectrum.ext; rfl
  right_inv Q := by apply Subtype.ext; rfl

/-- A completely split finite prime has one prime above it for every relative degree. -/
theorem card_heightPrimesOver_of_splitsCompletely
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hs : ClassFieldTheory.FinitePrimeSplitsCompletely K L v) :
    Nat.card {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} =
      Module.finrank K L := by
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨Q, hQmax, hQlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 L) v.asIdeal
  let : Q.IsPrime := hQmax.isPrime
  let : Q.LiesOver v.asIdeal := hQlo
  let w : HeightOneSpectrum (𝓞 L) :=
    ⟨Q, hQmax.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  obtain ⟨he, hf⟩ := hs w hQlo
  have hcard := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.asIdeal (𝓞 L) (L ≃ₐ[K] L)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q (L ≃ₐ[K] L), he, hf,
    one_mul, mul_one, IsGalois.card_aut_eq_finrank] at hcard
  exact (Nat.card_congr (heightPrimesOverEquiv L v)).trans
    ((Nat.card_coe_set_eq _).trans hcard)

/-- If all norm-p primes of the base completely split, contraction counts
the norm-p prime ideals of the extension by the relative degree. -/
theorem card_prime_norm_fiber_mul_relative_degree
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime)
    (hs : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm = p →
      ClassFieldTheory.FinitePrimeSplitsCompletely K L v) :
    Nat.card {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.absNorm = p} =
      Nat.card {v : HeightOneSpectrum (𝓞 K) // v.asIdeal.absNorm = p} *
        Module.finrank K L := by
  classical
  have : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let A := {v : HeightOneSpectrum (𝓞 K) // v.asIdeal.absNorm = p}
  let B := {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.absNorm = p}
  have : Finite {I : Ideal (𝓞 K) // I.absNorm = p} :=
    (Ideal.finite_setOfPred_absNorm_eq p).to_subtype
  have : Finite A := Finite.of_injective
    (fun v : A => (⟨v.1.asIdeal, v.2⟩ : {I : Ideal (𝓞 K) // I.absNorm = p}))
    (by intro v w h; apply Subtype.ext; apply HeightOneSpectrum.ext
        exact congrArg Subtype.val h)
  let : Fintype A := Fintype.ofFinite A
  let f : B → A := fun w =>
    ⟨w.1.under (𝓞 K), (prime_norm_under_and_inertiaDeg L hp w.1 w.2).1⟩
  let F : A → Type _ := fun v => {w : B // f w = v}
  have e (v : A) : F v ≃ {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal} := by
    have hnorm (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
        w.1.asIdeal.absNorm = p := by
      let : w.1.asIdeal.LiesOver v.1.asIdeal := w.2
      have hpow := Ideal.absNorm_pow_inertiaDeg v.1.asIdeal w.1.asIdeal
      rw [(hs v.1 v.2 w.1 w.2).2, pow_one, v.2] at hpow
      exact hpow.symm
    refine
      { toFun := fun w => ⟨w.1.1, ⟨(congrArg (fun v : A => v.1.asIdeal) w.2).symm⟩⟩
        invFun := fun w => ⟨⟨w.1, hnorm w⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · apply Subtype.ext
      apply HeightOneSpectrum.ext
      exact w.2.over.symm
    · intro w
      apply Subtype.ext
      apply Subtype.ext
      rfl
    · intro w
      apply Subtype.ext
      rfl
  have hfinite (v : A) : Finite (F v) := by
    have := Finite.of_equiv (v.1.asIdeal.primesOver (𝓞 L)) (heightPrimesOverEquiv L v.1).symm
    exact Finite.of_equiv _ (e v).symm
  calc
    Nat.card B = Nat.card (Σ v : A, F v) := (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ v : A, Nat.card (F v) := Nat.card_sigma
    _ = ∑ _v : A, Module.finrank K L := by
      apply Finset.sum_congr rfl
      intro v _
      exact (Nat.card_congr (e v)).trans (card_heightPrimesOver_of_splitsCompletely L v.1 (hs v.1 v.2))
    _ = Nat.card A * Module.finrank K L := by simp [Nat.card_eq_fintype_card]

/-- Principality of a finite prime's fractional ideal is equivalent to
principality of the integral prime ideal itself. -/
theorem finitePrime_fractionalPrincipal_iff_isPrincipal
    (v : HeightOneSpectrum (𝓞 K)) :
    ClassFieldTheory.finitePrimeFractionalIdeal v ∈
      (toPrincipalIdeal (𝓞 K) K).range ↔ v.asIdeal.IsPrincipal := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := mem_principal_ideals_iff.mp h
    change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x =
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) at hx
    have hm : x ∈ (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      rw [← hx]
      exact FractionalIdeal.mem_spanSingleton_self _ _
    obtain ⟨a, ha, hax⟩ := (FractionalIdeal.mem_coeIdeal _).mp hm
    refine ⟨⟨a, ?_⟩⟩
    change v.asIdeal = Ideal.span {a}
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [FractionalIdeal.coeIdeal_span_singleton, hax]
    exact hx.symm
  · intro h
    let := h
    apply mem_principal_ideals_iff.mpr
    refine ⟨((Submodule.IsPrincipal.generator v.asIdeal : 𝓞 K) : K), ?_⟩
    change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
      (algebraMap (𝓞 K) K (Submodule.IsPrincipal.generator v.asIdeal)) =
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_generator]

end QuadraticMoat

namespace QuadraticMoat

/-- Native norm-p prime fibers in the two equivalent prime-ideal presentations. -/
noncomputable def primeNormFiberHeightEquiv (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    {P : PrimeNormIdeal K // P.1.absNorm = p} ≃
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // v.asIdeal.absNorm = p} where
  toFun P := ⟨⟨P.1.1, P.1.2.2.1, P.1.2.2.2⟩, P.2⟩
  invFun v := ⟨⟨v.1.asIdeal, by rw [v.2]; exact hp, v.1.isPrime, v.1.ne_bot⟩, v.2⟩
  left_inv P := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; apply IsDedekindDomain.HeightOneSpectrum.ext; rfl

/-- A degree-one prime of a small Hilbert class field above a good rational
prime yields the native principal splitting package in the quadratic base. -/
theorem smallHilbert_splitPrime_of_prime_norm
    (K : Type) [Field K] [NumberField K]
    (E : ClassFieldTheory.FiniteAbelianExtension K)
    (hE : ClassFieldTheory.IsSmallHilbertClassField E)
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (hn : w.asIdeal.absNorm = p) :
    Nonempty (SplitPrime K p) := by
  have hs := prime_norm_splits_completely_of_unramified E hE.1.1 hp w hn
  have hprin := (ClassFieldTheory.finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal
    K E hE (w.under (𝓞 K))).mp hs
  exact splitPrime_of_principal_prime_norm_of_not_dvd_discr hdegree hp hdisc
    (w.under (𝓞 K)) (finitePrime_fractionalPrincipal_iff_isPrincipal _ |>.mp hprin)
    (prime_norm_under_and_inertiaDeg E hp w hn).1

/-- The exact degree-one prime-ideal fiber count in the small Hilbert class
field of a quadratic number field, away from its discriminant. -/
theorem smallHilbert_prime_norm_height_fiber_card
    (K : Type) [Field K] [NumberField K]
    (E : ClassFieldTheory.FiniteAbelianExtension K)
    (hE : ClassFieldTheory.IsSmallHilbertClassField E)
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K) :
    Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // w.asIdeal.absNorm = p} =
      if Nonempty (SplitPrime K p) then Module.finrank ℚ E else 0 := by
  classical
  by_cases hsplit : Nonempty (SplitPrime K p)
  · obtain ⟨P⟩ := hsplit
    have hs (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hn : v.asIdeal.absNorm = p) :
        ClassFieldTheory.FinitePrimeSplitsCompletely K E v := by
      apply (ClassFieldTheory.finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal
        K E hE v).mpr
      exact (finitePrime_fractionalPrincipal_iff_isPrincipal v).mpr
        (prime_norm_isPrincipal_of_splitPrime P v hn)
    rw [if_pos (show Nonempty (SplitPrime K p) from ⟨P⟩), card_prime_norm_fiber_mul_relative_degree E hp hs,
      card_prime_norm_fiber_of_splitPrime P]
    simpa only [hdegree] using Module.finrank_mul_finrank ℚ K E
  · have hempty : IsEmpty {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // w.asIdeal.absNorm = p} :=
      ⟨fun w => hsplit (smallHilbert_splitPrime_of_prime_norm K E hE hdegree hp hdisc w.1 w.2)⟩
    let := hempty
    rw [if_neg hsplit, Nat.card_of_isEmpty]

/-- The exact multiplicity needed to transfer the Hilbert prime-ideal
regularized series to the principal-split rational-prime coefficient. -/
theorem smallHilbert_primeNormMultiplicity
    (K : Type) [Field K] [NumberField K]
    (E : ClassFieldTheory.FiniteAbelianExtension K)
    (hE : ClassFieldTheory.IsSmallHilbertClassField E)
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K) :
    primeNormMultiplicity E p =
      if Nonempty (SplitPrime K p) then Module.finrank ℚ E else 0 := by
  unfold primeNormMultiplicity
  rw [Nat.card_congr (primeNormFiberHeightEquiv E hp)]
  exact smallHilbert_prime_norm_height_fiber_card K E hE hdegree hp hdisc

/-- A concrete finite exceptional set for the rational-prime count formula. -/
noncomputable def discriminantDivisors (K : Type*) [Field K] [NumberField K] : Finset ℕ :=
  (NumberField.discr K).natAbs.divisors

theorem not_dvd_discr_of_not_mem_discriminantDivisors
    (K : Type*) [Field K] [NumberField K] {p : ℕ}
    (hp : p ∉ discriminantDivisors K) : ¬ (p : ℤ) ∣ NumberField.discr K := by
  intro hd
  apply hp
  exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hd,
    Int.natAbs_eq_zero.not.mpr (NumberField.discr_ne_zero K)⟩

/-- The complete coefficient bridge, including nonprime rational integers. -/
theorem smallHilbert_primeNormMultiplicity_real_off_discriminant
    (K : Type) [Field K] [NumberField K]
    (E : ClassFieldTheory.FiniteAbelianExtension K)
    (hE : ClassFieldTheory.IsSmallHilbertClassField E)
    (hdegree : Module.finrank ℚ K = 2) {p : ℕ}
    (hpbad : p ∉ discriminantDivisors K) :
    (primeNormMultiplicity E p : ℝ) = (Module.finrank ℚ E : ℝ) *
      (if Nonempty (SplitPrime K p) then 1 else 0) := by
  classical
  by_cases hp : p.Prime
  · rw [smallHilbert_primeNormMultiplicity K E hE hdegree hp
      (not_dvd_discr_of_not_mem_discriminantDivisors K hpbad)]
    split_ifs <;> simp
  · have hs : ¬ Nonempty (SplitPrime K p) := fun ⟨P⟩ => hp P.prime
    simp [primeNormMultiplicity_zero_of_not_prime E hp, hs]

end QuadraticMoat
