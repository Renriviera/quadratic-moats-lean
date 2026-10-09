import QuadraticMoat.BoundedFactors.Model
import QuadraticMoat.DyadicSieve

/-! Each selected coprime prime generator charges one distinct prime ideal. -/

namespace QuadraticMoat.BoundedFactors

open NumberField UniqueFactorizationMonoid
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

noncomputable def principalIdeal (f : 𝓞 K) : Ideal (𝓞 K) :=
  Ideal.span ({f} : Set (𝓞 K))

noncomputable def finiteFactorHitCount (F : Finset (𝓞 K)) (α : 𝓞 K) : ℕ :=
  (F.filter (fun f => f ∣ α)).card

theorem principalIdeal_mem_support {α f : 𝓞 K} (hα : α ≠ 0) (hf : Prime f)
    (hdiv : f ∣ α) :
    principalIdeal f ∈ (normalizedFactors (principalIdeal α)).toFinset := by
  rw [Multiset.mem_toFinset]
  apply (Ideal.mem_normalizedFactors_iff (by simpa [principalIdeal] using hα)).mpr
  exact ⟨Ideal.isPrime_span_singleton_of_prime hf,
    (Ideal.span_singleton_le_iff_mem (principalIdeal f)).mpr (Ideal.mem_span_singleton.mpr hdiv)⟩

/-- Coprime nonunit generators have distinct principal ideals. -/
theorem principalIdeal_injOn {F : Finset (𝓞 K)}
    (hprime : ∀ f ∈ F, Prime f) (hcop : (F : Set (𝓞 K)).Pairwise IsCoprime) :
    Set.InjOn principalIdeal (F : Set (𝓞 K)) := by
  intro f hf g hg heq
  by_contra hne
  have hd : f ∣ g := Ideal.mem_span_singleton.mp (show g ∈ principalIdeal f from
    heq.symm ▸ Ideal.subset_span (Set.mem_singleton g))
  exact (hprime f hf).not_isUnit ((hcop hf hg hne).isUnit_of_dvd hd)

/-- Selected-factor hits are bounded by distinct ideal support, regardless of valuations. -/
theorem finiteFactorHitCount_le_omega {F : Finset (𝓞 K)}
    (hprime : ∀ f ∈ F, Prime f) (hcop : (F : Set (𝓞 K)).Pairwise IsCoprime)
    {α : 𝓞 K} (hα : α ≠ 0) : finiteFactorHitCount F α ≤ omega K α := by
  have hinj := principalIdeal_injOn hprime hcop
  have hsub : (F.filter (fun f => f ∣ α)).image principalIdeal ⊆
      (normalizedFactors (principalIdeal α)).toFinset := by
    intro P hP
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hfF, hfα⟩ := Finset.mem_filter.mp hf
    exact principalIdeal_mem_support hα (hprime f hfF) hfα
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (hinj.mono (by
    intro f hf
    exact (Finset.mem_filter.mp hf).1))] at hc
  exact hc

end QuadraticMoat.BoundedFactors

namespace QuadraticMoat.SplitSieve

open NumberField
open scoped Classical
variable {K : Type*} [Field K] [NumberField K]

theorem factor_coprime_of_indices_ne (s : SplitSieve K)
    {p q : ℕ} (hp : p ∈ s.primes) (hq : q ∈ s.primes)
    {i j : Fin 2} (hne : (p, i) ≠ (q, j)) :
    IsCoprime (s.factor p i) (s.factor q j) := by
  rw [s.factor_eq p hp, s.factor_eq q hq]
  by_cases hpq : p = q
  · subst q
    have hij : i ≠ j := by intro hij; exact hne (by simp [hij])
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact (s.packet ⟨p, hp⟩).coprime
    · exact (s.packet ⟨p, hp⟩).coprime.symm
    · exact False.elim (hij rfl)
  · exact (s.packet ⟨p, hp⟩).factors_coprime (s.packet ⟨q, hq⟩) hpq i j

theorem selectedFactors_prime (s : SplitSieve K) :
    ∀ f ∈ s.selectedFactors, Prime f := by
  intro f hf
  obtain ⟨p, hp, i, rfl⟩ := (s.mem_selectedFactors f).mp hf
  exact s.factor_prime p hp i

theorem selectedFactors_pairwise_coprime (s : SplitSieve K) :
    (s.selectedFactors : Set (𝓞 K)).Pairwise IsCoprime := by
  intro f hf g hg hfg
  obtain ⟨p, hp, i, rfl⟩ := (s.mem_selectedFactors f).mp hf
  obtain ⟨q, hq, j, rfl⟩ := (s.mem_selectedFactors g).mp hg
  apply s.factor_coprime_of_indices_ne hp hq
  intro heq
  apply hfg
  cases heq
  rfl

theorem selectedFactors_principalIdeal_injOn (s : SplitSieve K) :
    Set.InjOn BoundedFactors.principalIdeal (s.selectedFactors : Set (𝓞 K)) :=
  BoundedFactors.principalIdeal_injOn s.selectedFactors_prime s.selectedFactors_pairwise_coprime

theorem selectedFactors_hitCount_le_omega (s : SplitSieve K) {α : 𝓞 K} (hα : α ≠ 0) :
    BoundedFactors.finiteFactorHitCount s.selectedFactors α ≤ BoundedFactors.omega K α :=
  BoundedFactors.finiteFactorHitCount_le_omega s.selectedFactors_prime
    s.selectedFactors_pairwise_coprime hα

/-- Batches selecting disjoint rational primes have disjoint factor sets. -/
theorem selectedFactors_disjoint_of_primes_disjoint (s t : SplitSieve K)
    (h : Disjoint s.primes t.primes) : Disjoint s.selectedFactors t.selectedFactors := by
  apply Finset.disjoint_left.mpr
  intro f hf hg
  obtain ⟨p, hp, i, hpi⟩ := (s.mem_selectedFactors f).mp hf
  obtain ⟨q, hq, j, hqj⟩ := (t.mem_selectedFactors f).mp hg
  have hpq : p = q := by
    calc
      p = integerAbsNorm K f := by rw [← hpi, s.factor_norm p hp i]
      _ = q := by rw [← hqj, t.factor_norm q hq j]
  exact Finset.disjoint_left.mp h hp (by simpa only [hpq] using hq)

/-- The finite union of disjoint-prime batches still charges distinct ideals. -/
theorem biUnion_selectedFactors_pairwise_coprime {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (s : ι → SplitSieve K)
    (h : (J : Set ι).Pairwise (fun i j => Disjoint (s i).primes (s j).primes)) :
    ((J.biUnion (fun i => (s i).selectedFactors)) : Set (𝓞 K)).Pairwise IsCoprime := by
  intro f hf g hg hfg
  obtain ⟨a, ha, hf⟩ := Finset.mem_biUnion.mp hf
  obtain ⟨c, hc, hg⟩ := Finset.mem_biUnion.mp hg
  by_cases hac : a = c
  · subst c
    exact (s a).selectedFactors_pairwise_coprime hf hg hfg
  · obtain ⟨p, hp, i, rfl⟩ := ((s a).mem_selectedFactors f).mp hf
    obtain ⟨q, hq, j, rfl⟩ := ((s c).mem_selectedFactors g).mp hg
    have hpq : p ≠ q := by
      intro hpq
      exact Finset.disjoint_left.mp (h ha hc hac) hp (by simpa only [hpq] using hq)
    rw [(s a).factor_eq p hp, (s c).factor_eq q hq]
    exact ((s a).packet ⟨p, hp⟩).factors_coprime ((s c).packet ⟨q, hq⟩) hpq i j

theorem biUnion_selectedFactors_prime {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (s : ι → SplitSieve K) :
    ∀ f ∈ J.biUnion (fun i => (s i).selectedFactors), Prime f := by
  intro f hf
  obtain ⟨i, _, hf⟩ := Finset.mem_biUnion.mp hf
  exact (s i).selectedFactors_prime f hf


end QuadraticMoat.SplitSieve

namespace QuadraticMoat.PrimeFamily

open NumberField
open scoped Classical
variable {K : Type*} [Field K] [NumberField K]

theorem dyadicBatch_disjoint (F : PrimeFamily) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (F.dyadicBatch j) (F.dyadicBatch k) := by
  apply Finset.disjoint_left.mpr
  intro p hpj hpk
  have hj := (F.mem_dyadicBatch j p).mp hpj
  have hk := (F.mem_dyadicBatch k p).mp hpk
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · exact (not_lt_of_ge ((pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ))
      (Nat.succ_le_of_lt hlt)).trans hk.1)) hj.2.1
  · exact (not_lt_of_ge ((pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ))
      (Nat.succ_le_of_lt hgt)).trans hj.1)) hk.2.1

theorem dyadicSieve_primes_pairwise_disjoint (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (J : Finset ℕ) :
    (J : Set ℕ).Pairwise (fun j k => Disjoint (F.dyadicSieve hgood j).primes
      (F.dyadicSieve hgood k).primes) := by
  intro j _ k _ hjk
  exact F.dyadicBatch_disjoint hjk

theorem dyadicSieve_selectedFactors_pairwise_disjoint (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (J : Finset ℕ) :
    (J : Set ℕ).Pairwise (fun j k => Disjoint (F.dyadicSieve hgood j).selectedFactors
      (F.dyadicSieve hgood k).selectedFactors) := by
  intro j _ k _ hjk
  exact SplitSieve.selectedFactors_disjoint_of_primes_disjoint _ _
    (F.dyadicBatch_disjoint hjk)

end QuadraticMoat.PrimeFamily
