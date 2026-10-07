import QuadraticMoat.DenseBins
import QuadraticMoat.SignedSieve
import QuadraticMoat.WalkWords
import QuadraticMoat.PointEnrichment

namespace QuadraticMoat
open scoped Classical BigOperators
open OAI.GaussianMoat
open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Choose actual principal split factors for a finite supplied prime set. -/
noncomputable def splitSieveOf (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nonempty (SplitPrime K p)) : SplitSieve K where
  primes := S
  packet p := (hS p.val p.property).some

/-- Native arithmetic sieve for one dyadic batch of a prime family. -/
noncomputable def PrimeFamily.dyadicSieve (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (j : ℕ) : SplitSieve K :=
  splitSieveOf (F.dyadicBatch j) (fun p hp => hgood p
    ((F.mem_dyadicBatch j p).mp hp).2.2.2)

@[simp] theorem PrimeFamily.dyadicSieve_primes (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (j : ℕ) :
    (F.dyadicSieve hgood j).primes = F.dyadicBatch j := rfl

lemma dyadic_prime_bounds (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (j : ℕ) :
    ∀ p ∈ (F.dyadicSieve hgood j).primes,
      (2 : ℝ)^j ≤ p ∧ (p : ℝ) ≤ 2*(2 : ℝ)^j := by
  intro p hp
  have hh := (F.mem_dyadicBatch j p).mp hp
  constructor
  · exact_mod_cast hh.1
  · have hh' : p ≤ 2^(j+1) := hh.2.1.le
    rw [pow_succ] at hh'
    exact_mod_cast (by simpa only [mul_comm] using hh' : p ≤ 2*2^j)

lemma dyadic_dense_nonempty (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) {δ : ℝ} (hδ : 0 < δ) {j : ℕ}
    (hd : δ*(2 : ℝ)^j / Real.log ((2 : ℝ)^(j+1)) ≤ (F.dyadicBatch j).card) :
    (F.dyadicSieve hgood j).primes.Nonempty := by
  apply Finset.card_pos.mp
  have hp : 0 < δ*(2 : ℝ)^j / Real.log ((2 : ℝ)^(j+1)) := by
    rw [Real.log_pow]
    positivity
  exact_mod_cast hp.trans_le hd

lemma dyadic_mean_bounds (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) {X : ℝ} (hX : 2 ≤ X) {j : ℕ}
    (hne : (F.dyadicSieve hgood j).primes.Nonempty)
    (hlo : X ≤ j*Real.log 2) (hhi : j*Real.log 2 ≤ 21/20*X) :
    1 ≤ (F.dyadicSieve hgood j).meanLog ∧ (F.dyadicSieve hgood j).meanLog ≤ 2*X := by
  have hh := (F.dyadicSieve hgood j).meanLog_bounds hne (by positivity)
    (dyadic_prime_bounds F hgood j)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  constructor <;> linarith only [hh.1, hh.2, hlo, hhi, hX, hl2]

lemma integer_norm_log_nonneg (f : 𝓞 K) : 0 ≤ Real.log (integerAbsNorm K f) := by
  by_cases h : integerAbsNorm K f = 0
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)

noncomputable def residueWeight (F : Finset (𝓞 K)) : ℝ :=
  ∑ f ∈ F, Real.log (integerAbsNorm K f)

lemma residueWeight_mono {F G : Finset (𝓞 K)} (h : F ⊆ G) :
    residueWeight F ≤ residueWeight G :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun f _ _ => integer_norm_log_nonneg f)

lemma residueWeight_nonneg (F : Finset (𝓞 K)) : 0 ≤ residueWeight F :=
  Finset.sum_nonneg (fun f _ => integer_norm_log_nonneg f)

theorem residue_vector_entropy {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (z : Ω → 𝓞 K) (f : ι → 𝓞 K) (hf : ∀ i, f i ≠ 0) :
    p.Hf (fun ω i => residueCode (f i) (z ω)) ≤
      ∑ i, Real.log (integerAbsNorm K (f i)) := by
  let (i : ι) : Finite ((𝓞 K) ⧸ multiples (f i)) := finite_ringResidue (hf i)
  let (i : ι) : Fintype ((𝓞 K) ⧸ multiples (f i)) := Fintype.ofFinite _
  rw [p.Hf_eq_of_fibers _ (fun ω i => ringResidue (f i) (z ω))
    (fun ω ν => by simp only [funext_iff, residueCode_eq, ringResidue_eq])]
  have hh := p.Hf_le_log_card_type (fun ω i => ringResidue (f i) (z ω))
  rw [Fintype.card_pi, Nat.cast_prod, Real.log_prod] at hh
  · convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.card_eq_fintype_card, multiples_index]
  · intro i _
    exact_mod_cast Fintype.card_ne_zero

lemma residue_finset_entropy {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (z : Ω → 𝓞 K) (F : Finset (𝓞 K)) (hf : ∀ f ∈ F, f ≠ 0) :
    p.Hf (fun ω (f : F) => residueCode f.val (z ω)) ≤ residueWeight F := by
  have h := residue_vector_entropy p z (fun f : F => f.val) (fun f => hf f.val f.property)
  exact h.trans_eq (Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun f : 𝓞 K => Real.log (integerAbsNorm K f))).symm

lemma SplitSieve.selectedFactors_ne_zero (s : SplitSieve K) {f : 𝓞 K}
    (hf : f ∈ s.selectedFactors) : f ≠ 0 := by
  obtain ⟨p, hp, i, rfl⟩ := (s.mem_selectedFactors f).mp hf
  exact (s.factor_prime p hp i).ne_zero

lemma SplitSieve.selectedFactors_weight (s : SplitSieve K) :
    residueWeight s.selectedFactors ≤ 2 * ∑ p ∈ s.primes, Real.log (p : ℝ) := by
  have heq : s.selectedFactors =
      Finset.univ.image (fun i : s.primes × Fin 2 => s.factor i.1.val i.2) := by
    ext f
    simp only [s.mem_selectedFactors, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, i, rfl⟩
      exact ⟨(⟨p, hp⟩, i), rfl⟩
    · rintro ⟨⟨p, i⟩, rfl⟩
      exact ⟨p.val, p.property, i, rfl⟩
  have h := Finset.sum_image_le_of_nonneg (s := (Finset.univ : Finset (s.primes × Fin 2)))
    (g := fun i : s.primes × Fin 2 => s.factor i.1.val i.2)
    (f := fun f => Real.log (integerAbsNorm K f))
    (fun f _ => integer_norm_log_nonneg f)
  rw [residueWeight, heq]
  apply h.trans_eq
  simp only [Fintype.sum_prod_type, s.factor_norm _ (Subtype.property _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [Finset.mul_sum]
  exact (Finset.sum_subtype s.primes (fun _ => Iff.rfl)
    (fun p : ℕ => 2 * Real.log (p : ℝ))).symm

lemma dyadicSieve_available_weight (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (j : ℕ) :
    residueWeight (F.dyadicSieve hgood j).selectedFactors ≤
      4*Real.log 4*(2 : ℝ)^j := by
  have hp : (∑ p ∈ F.dyadicBatch j, Real.log (p : ℝ)) ≤ Real.log 4*(2 : ℝ)^(j+1) :=
    OAI.GaussianMoat.PrimeLogMass.prime_log_mass_le_theta _ (by positivity) (by
      intro p hp
      have h := (F.mem_dyadicBatch j p).mp hp
      exact ⟨h.2.2.1, by exact_mod_cast h.2.1.le⟩)
  have hh := (F.dyadicSieve hgood j).selectedFactors_weight
  change residueWeight (F.dyadicSieve hgood j).selectedFactors ≤
    2*∑ p ∈ F.dyadicBatch j, Real.log (p : ℝ) at hh
  rw [pow_succ] at hp
  nlinarith only [hh, hp]

end QuadraticMoat
