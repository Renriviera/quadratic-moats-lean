import QuadraticMoat.PrimeNormSeries

namespace QuadraticMoat
open NumberField

variable (K : Type*) [Field K] [NumberField K]

lemma primeNorm_fiber_under_span (n : ℕ) (hn : n.Prime)
    (P : {P : PrimeNormIdeal K // P.1.absNorm = n}) :
    P.1.1.under ℤ = Ideal.span {(n : ℤ)} := by
  let : P.1.1.IsPrime := P.1.2.2.1
  let : NeZero P.1.1 := ⟨P.1.2.2.2⟩
  have hp := Nat.absNorm_under_prime P.1.1
  have hdiv : (P.1.1.under ℤ).absNorm ∣ n := by
    simpa only [P.2] using Int.absNorm_under_dvd_absNorm P.1.1
  have hnorm := (Nat.prime_dvd_prime_iff_eq hp hn).mp hdiv
  rw [← Int.ideal_span_absNorm_eq_self (P.1.1.under ℤ), hnorm]

/-- The number of prime ideals with a specified rational-prime norm is
at most the absolute degree of the number field. -/
theorem primeNormMultiplicity_le_finrank (n : ℕ) :
    primeNormMultiplicity K n ≤ Module.finrank ℚ K := by
  classical
  by_cases hn : n.Prime
  · let A := {P : PrimeNormIdeal K // P.1.absNorm = n}
    cases isEmpty_or_nonempty A with
    | inl hA =>
      let := hA
      change Nat.card A ≤ _
      simp
    | inr hA =>
      let P₀ : A := Classical.choice hA
      let p : Ideal ℤ := Ideal.span {(n : ℤ)}
      have hp : p.IsPrime := by
        dsimp [p]
        rw [← primeNorm_fiber_under_span K n hn P₀]
        let : P₀.1.1.IsPrime := P₀.1.2.2.1
        infer_instance
      let := hp
      have hp0 : p ≠ ⊥ := by
        dsimp [p]
        rw [← primeNorm_fiber_under_span K n hn P₀]
        exact Ideal.IsIntegral.under_ne_bot ℤ P₀.1.2.2.2
      let : p.IsMaximal := hp.isMaximal hp0
      let f : A → p.primesOver (𝓞 K) := fun P =>
        ⟨P.1.1, P.1.2.2.1, ⟨by
          exact (primeNorm_fiber_under_span K n hn P) ▸
            (Ideal.over_under (A := ℤ) (P := P.1.1)).over⟩⟩
      have hfinj : Function.Injective f := by
        intro P Q h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun I : p.primesOver (𝓞 K) => I.1) h
      let : Finite (p.primesOver (𝓞 K)) :=
        (IsDedekindDomain.primesOver_finite p _).to_subtype
      let : Fintype (p.primesOver (𝓞 K)) := Fintype.ofFinite _
      have hcard : Nat.card (p.primesOver (𝓞 K)) ≤ Module.finrank ℚ K := by
        calc
          Nat.card (p.primesOver (𝓞 K)) = ∑ _q : p.primesOver (𝓞 K), (1 : ℕ) := by
            simp [Nat.card_eq_fintype_card]
          _ ≤ ∑ q : p.primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
            apply Finset.sum_le_sum
            intro q _
            let : q.1.IsPrime := q.2.1
            exact Nat.mul_pos (Ideal.ramificationIdx_pos q.1 ℤ) (Ideal.inertiaDeg_pos q.1 ℤ)
          _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)
          _ = Module.finrank ℚ K := RingOfIntegers.rank K
      exact (Nat.card_le_card_of_injective f hfinj).trans hcard
  · rw [primeNormMultiplicity_zero_of_not_prime K hn]
    exact Nat.zero_le _

end QuadraticMoat
