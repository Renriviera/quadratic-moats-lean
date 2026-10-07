import QuadraticMoat.SplitArithmetic
import QuadraticMoat.PlanarGeometry
import QuadraticMoat.CoordinateNorm
import QuadraticMoat.Periodicity
import OAI.NumberTheory.GaussianMoat.SignedGeometry

/-! Native principal-split-factor sieves and their random signed arithmetic. -/

namespace QuadraticMoat

open NumberField MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {K : Type*} [Field K] [NumberField K]

structure SplitSieve (K : Type*) [Field K] [NumberField K] where
  primes : Finset ℕ
  packet : ∀ p : primes, SplitPrime K p.val

namespace SplitSieve

noncomputable def factor (s : SplitSieve K) (p : ℕ) : Fin 2 → 𝓞 K :=
  if hp : p ∈ s.primes then (s.packet ⟨p, hp⟩).factor else fun _ => 0

theorem factor_eq (s : SplitSieve K) (p : ℕ) (hp : p ∈ s.primes) :
    s.factor p = (s.packet ⟨p, hp⟩).factor := by simp only [factor, dite_eq_left hp]

theorem prime_mem (s : SplitSieve K) (p : ℕ) (hp : p ∈ s.primes) : p.Prime :=
  (s.packet ⟨p, hp⟩).prime

theorem factor_norm (s : SplitSieve K) (p : ℕ) (hp : p ∈ s.primes) (i : Fin 2) :
    integerAbsNorm K (s.factor p i) = p := by
  rw [s.factor_eq p hp]
  exact (s.packet ⟨p, hp⟩).factor_norm i

theorem factor_prime (s : SplitSieve K) (p : ℕ) (hp : p ∈ s.primes) (i : Fin 2) :
    Prime (s.factor p i) := by
  rw [s.factor_eq p hp]
  exact (s.packet ⟨p, hp⟩).factor_prime i

def period (s : SplitSieve K) : ℕ := ∏ p ∈ s.primes, p

theorem period_pos (s : SplitSieve K) : 0 < s.period :=
  Finset.prod_pos (fun p hp => (s.prime_mem p hp).pos)

end SplitSieve

def signedFactor (f : Fin 2 → 𝓞 K) (choice : Bool) : 𝓞 K := f (if choice then 0 else 1)

theorem SplitSieve.signedFactor_norm (s : SplitSieve K) (p : ℕ) (hp : p ∈ s.primes)
    (choice : Bool) : integerAbsNorm K (signedFactor (s.factor p) choice) = p :=
  s.factor_norm p hp _

theorem SplitSieve.signedFactor_prime (s : SplitSieve K) (p : ℕ) (hp : p ∈ s.primes)
    (choice : Bool) : Prime (signedFactor (s.factor p) choice) := s.factor_prime p hp _

theorem SplitSieve.factors_coprime (s : SplitSieve K) (p q : ℕ)
    (hp : p ∈ s.primes) (hq : q ∈ s.primes) (hpq : p ≠ q) (choice choice' : Bool) :
    IsCoprime (signedFactor (s.factor p) choice) (signedFactor (s.factor q) choice') := by
  unfold signedFactor
  rw [s.factor_eq p hp, s.factor_eq q hq]
  exact (s.packet ⟨p, hp⟩).factors_coprime (s.packet ⟨q, hq⟩) hpq _ _

theorem SplitSieve.prod_factors_dvd (s : SplitSieve K) (t : Finset ℕ) (ht : t ⊆ s.primes)
    (σ : ℕ → Bool) {v : 𝓞 K}
    (hd : ∀ p ∈ t, signedFactor (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ v := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro p hp q hq hpq
  exact s.factors_coprime p q (ht hp) (ht hq) hpq _ _

theorem SplitSieve.eligible_product_le_norm (s : SplitSieve K) (t : Finset ℕ)
    (ht : t ⊆ s.primes) (σ : ℕ → Bool) {v : 𝓞 K} (hv : v ≠ 0)
    (hd : ∀ p ∈ t, signedFactor (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t, p) ≤ integerAbsNorm K v := by
  have hle := integerAbsNorm_le_of_dvd hv (s.prod_factors_dvd t ht σ hd)
  rw [map_prod] at hle
  convert hle using 1
  exact Finset.prod_congr rfl (fun p hp => (s.signedFactor_norm p (ht hp) _).symm)

omit [NumberField K] in
/-- Coordinate determinant agrees with the Gaussian lattice coordinate determinant. -/
theorem basisDet_eq_coordinate_determinant (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (v w : 𝓞 K) :
    basisDet b v w = OAI.GaussianMoat.determinant (coordinateGaussian b v) (coordinateGaussian b w) := by
  simp only [basisDet, OAI.GaussianMoat.determinant, coordinateGaussian_re, coordinateGaussian_im]

omit [NumberField K] in
theorem primitive_iff_coordinate_primitive (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (v : 𝓞 K) :
    CoordinatePrimitive b v ↔ OAI.GaussianMoat.PrimitiveDirection (coordinateGaussian b v) := by
  simp only [CoordinatePrimitive, OAI.GaussianMoat.PrimitiveDirection,
    coordinateGaussian_re, coordinateGaussian_im]

omit [NumberField K] in
/-- A primitive integer-coordinate line has only integer multiples as lattice points. -/
theorem int_multiple_of_basisDet_zero (b : Module.Basis (Fin 2) ℤ (𝓞 K)) {v w : 𝓞 K}
    (hv : CoordinatePrimitive b v) (hvw : basisDet b v w = 0) :
    ∃ a : ℤ, w = (a : 𝓞 K) * v := by
  have hgdet : OAI.GaussianMoat.determinant (coordinateGaussian b v) (coordinateGaussian b w) = 0 := by
    rw [← basisDet_eq_coordinate_determinant]
    exact hvw
  obtain ⟨a, ha⟩ := OAI.GaussianMoat.int_multiple_of_determinant_zero
    ((primitive_iff_coordinate_primitive b v).mp hv)
    hgdet
  refine ⟨a, ?_⟩
  apply (coordinateGaussian b).injective
  rw [← zsmul_eq_mul, map_zsmul]
  simpa only [zsmul_eq_mul] using ha

omit [NumberField K] in
theorem exists_coordinate_primitive_direction (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    {w : 𝓞 K} (hw : w ≠ 0) :
    ∃ v : 𝓞 K, CoordinatePrimitive b v ∧ v ≠ 0 ∧
      ∃ a : ℤ, a ≠ 0 ∧ w = (a : 𝓞 K) * v := by
  have hgw : coordinateGaussian b w ≠ 0 := by
    intro hz
    apply hw
    exact (coordinateGaussian b).injective (by simpa only [map_zero] using hz)
  obtain ⟨v, hv, hv0, a, ha0, ha⟩ := OAI.GaussianMoat.exists_primitive_direction hgw
  refine ⟨(coordinateGaussian b).symm v, ?_, ?_, a, ha0, ?_⟩
  · rw [primitive_iff_coordinate_primitive]
    simpa only [LinearEquiv.apply_symm_apply] using hv
  · intro hz
    apply hv0
    simpa only [hz, map_zero, LinearEquiv.apply_symm_apply] using
      ((coordinateGaussian b).apply_symm_apply v).symm
  · apply (coordinateGaussian b).injective
    rw [← zsmul_eq_mul, map_zsmul, LinearEquiv.apply_symm_apply]
    simpa only [zsmul_eq_mul] using ha

theorem SplitSieve.factor_dvd_integer_iff (s : SplitSieve K) (p : ℕ) (hp : p ∈ s.primes)
    (choice : Bool) (a : ℤ) : signedFactor (s.factor p) choice ∣ (a : 𝓞 K) ↔ (p : ℤ) ∣ a := by
  unfold signedFactor
  rw [s.factor_eq p hp]
  exact (s.packet ⟨p, hp⟩).factor_dvd_intCast_iff _ a

theorem SplitSieve.not_both_factors_dvd_primitive (s : SplitSieve K)
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) {v : 𝓞 K} (hv : CoordinatePrimitive b v)
    (p : ℕ) (hp : p ∈ s.primes) : ¬ (s.factor p 0 ∣ v ∧ s.factor p 1 ∣ v) := by
  rw [s.factor_eq p hp]
  exact (s.packet ⟨p, hp⟩).not_both_dvd_coordinatePrimitive b hv

theorem SplitSieve.uneligible_product_dvd_coefficient (s : SplitSieve K)
    (t : Finset ℕ) (ht : t ⊆ s.primes) (σ : ℕ → Bool) (v : 𝓞 K) (a : ℤ)
    (hw : (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ (a : 𝓞 K) * v) :
    (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ∣ a := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    have hp' := s.prime_mem p (ht (Finset.mem_filter.mp hp).1)
    have hq' := s.prime_mem q (ht (Finset.mem_filter.mp hq).1)
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.Coprime p q
    exact (hp'.coprime_iff_not_dvd).mpr (fun h =>
      ((Nat.dvd_prime hq').mp h).elim hp'.ne_one hpq)
  · intro p hp
    obtain ⟨hpt, hpv⟩ := Finset.mem_filter.mp hp
    have hpp := ht hpt
    have hd : signedFactor (s.factor p) (σ p) ∣ (a : 𝓞 K) * v :=
      (Finset.dvd_prod_of_mem _ hpt).trans hw
    have ha := ((s.signedFactor_prime p hpp (σ p)).dvd_mul.mp hd).resolve_right hpv
    exact (s.factor_dvd_integer_iff p hpp (σ p) a).mp ha

theorem SplitSieve.line_witness_norm_lower (s : SplitSieve K)
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (t : Finset ℕ) (ht : t ⊆ s.primes) (σ : ℕ → Bool)
    {v w : 𝓞 K} (hv : CoordinatePrimitive b v) (hw : w ≠ 0)
    (hline : basisDet b v w = 0)
    (hdiv : (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ w) :
    (integerAbsNorm K v : ℤ) *
      (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ^ 2 ≤
      (integerAbsNorm K w : ℤ) := by
  classical
  obtain ⟨a, rfl⟩ := int_multiple_of_basisDet_zero b hv hline
  have ha : a ≠ 0 := by intro h; simp [h] at hw
  have hd := s.uneligible_product_dvd_coefficient t ht σ v a hdiv
  have habs : 0 < |a| := abs_pos.mpr ha
  have hle := Int.le_of_dvd habs ((dvd_abs _ _).mpr hd)
  have hprod : 0 ≤ ∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ) :=
    Finset.prod_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hs : (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_abs a]
  have hrank : Module.finrank ℤ (𝓞 K) = 2 := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  rw [integerAbsNorm_mul, integerAbsNorm_intCast, hrank]
  push_cast
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hs (Int.natCast_nonneg (integerAbsNorm K v))]

noncomputable def SplitSieve.eligible (s : SplitSieve K) (v : 𝓞 K) : Finset ℕ :=
  s.primes.filter (fun p => s.factor p 0 ∣ v ∨ s.factor p 1 ∣ v)

noncomputable def SplitSieve.lineLog (s : SplitSieve K) (v : 𝓞 K) (p : ℕ) (choice : Bool) : ℝ :=
  if signedFactor (s.factor p) choice ∣ v then Real.log p else 0

theorem SplitSieve.eligible_log_bound (s : SplitSieve K) {v : 𝓞 K} (hv : v ≠ 0) :
    ∑ p ∈ s.eligible v, Real.log (p : ℝ) ≤ Real.log (integerAbsNorm K v : ℝ) := by
  classical
  let σ : ℕ → Bool := fun p => decide (s.factor p 0 ∣ v)
  have hnorm := s.eligible_product_le_norm (s.eligible v)
    (Finset.filter_subset _ _) σ hv (by
      intro p hp
      obtain ⟨_, hleft | hright⟩ := Finset.mem_filter.mp hp
      · simp [σ, signedFactor, hleft]
      · by_cases hd : s.factor p 0 ∣ v
        · simp [σ, signedFactor, hd]
        · simpa [σ, signedFactor, hd] using hright)
  have hnorm' : ∏ p ∈ s.eligible v, (p : ℝ) ≤ (integerAbsNorm K v : ℝ) := by
    have h : ((∏ p ∈ s.eligible v, p : ℕ) : ℝ) ≤ (integerAbsNorm K v : ℝ) := by
      exact_mod_cast hnorm
    simpa only [Nat.cast_prod] using h
  have hpos (p : ℕ) (hp : p ∈ s.eligible v) : 0 < (p : ℝ) := by
    exact_mod_cast (s.prime_mem p (Finset.mem_filter.mp hp).1).pos
  have hlog := Real.log_le_log (Finset.prod_pos hpos) hnorm'
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at hlog
  exact hlog

theorem SplitSieve.lineLog_mean (s : SplitSieve K) (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    {v : 𝓞 K} (hv : CoordinatePrimitive b v) (hv0 : v ≠ 0) :
    ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) / 2 ≤
      Real.log (integerAbsNorm K v : ℝ) / 2 := by
  classical
  have heq : ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) =
      ∑ p ∈ s.eligible v, Real.log (p : ℝ) := by
    rw [Finset.sum_coe_sort s.primes (fun p => s.lineLog v p false + s.lineLog v p true),
      SplitSieve.eligible, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hnot := s.not_both_factors_dvd_primitive b hv p hp
    by_cases h1 : s.factor p 0 ∣ v <;> by_cases h2 : s.factor p 1 ∣ v
    · exact False.elim (hnot ⟨h1, h2⟩)
    all_goals simp [SplitSieve.lineLog, signedFactor, h1, h2]
  rw [← Finset.sum_div, heq]
  exact div_le_div_of_nonneg_right (s.eligible_log_bound hv0) (by norm_num)

theorem SplitSieve.lineLog_tail (s : SplitSieve K) (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    {v : 𝓞 K} (hv : CoordinatePrimitive b v) (hv0 : v ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    (OAI.GaussianMoat.signMeasure s.primes).real {σ |
      Real.log (integerAbsNorm K v : ℝ) / 2 + ε ≤ ∑ p : s.primes, s.lineLog v p (σ p)} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ p : s.primes,
        (((‖Real.log (p : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  apply le_trans (measureReal_mono (s₂ := {σ |
    ε + ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) / 2 ≤
      ∑ p : s.primes, s.lineLog v p (σ p)}) ?_)
  · apply OAI.GaussianMoat.sign_hoeffding (fun p : s.primes => s.lineLog v p)
      (fun p => Real.log (p : ℝ))
    · intro p choice
      have hp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
        exact_mod_cast (s.prime_mem p p.property).one_lt.le)
      unfold SplitSieve.lineLog
      split_ifs
      · exact ⟨hp, le_rfl⟩
      · exact ⟨le_rfl, hp⟩
    · exact hε
  · intro σ hσ
    have hmean := s.lineLog_mean b hv hv0
    change Real.log (integerAbsNorm K v : ℝ) / 2 + ε ≤ _ at hσ
    change ε + _ ≤ _
    linarith

/-- The actual finite set of all selected principal split factors. -/
noncomputable def SplitSieve.selectedFactors (s : SplitSieve K) : Finset (𝓞 K) :=
  s.primes.biUnion (fun p => (Finset.univ : Finset (Fin 2)).image (s.factor p))

@[simp] theorem SplitSieve.mem_selectedFactors (s : SplitSieve K) (t : 𝓞 K) :
    t ∈ s.selectedFactors ↔ ∃ p ∈ s.primes, ∃ i : Fin 2, s.factor p i = t := by
  simp only [SplitSieve.selectedFactors, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and]

theorem SplitSieve.selectedFactor_nonunit (s : SplitSieve K) {t : 𝓞 K}
    (ht : t ∈ s.selectedFactors) : ¬ IsUnit t := by
  obtain ⟨p, hp, i, rfl⟩ := (s.mem_selectedFactors t).mp ht
  intro hu
  have hn := (integerAbsNorm_eq_one_iff_isUnit (s.factor p i)).mpr hu
  rw [s.factor_norm p hp i] at hn
  exact (s.prime_mem p hp).ne_one hn

theorem SplitSieve.selectedFactor_dvd_period (s : SplitSieve K) {t : 𝓞 K}
    (ht : t ∈ s.selectedFactors) : t ∣ (s.period : 𝓞 K) := by
  obtain ⟨p, hp, i, rfl⟩ := (s.mem_selectedFactors t).mp ht
  have hd : s.factor p i ∣ (p : 𝓞 K) := by
    rw [s.factor_eq p hp]
    exact (s.packet ⟨p, hp⟩).factor_dvd_natCast i
  exact hd.trans (map_dvd (Nat.castRingHom (𝓞 K)) (Finset.dvd_prod_of_mem id hp))

/-- Full-lattice vertices avoiding every factor of the finite split sieve. -/
def SplitSieve.avoiding (s : SplitSieve K) : Set (𝓞 K) :=
  integerAvoidingSelectedDivisors (s.selectedFactors : Set (𝓞 K))

theorem SplitSieve.mem_avoiding (s : SplitSieve K) (z : 𝓞 K) :
    z ∈ s.avoiding ↔ ∀ p ∈ s.primes, ∀ i : Fin 2, ¬ s.factor p i ∣ z := by
  constructor
  · intro hz p hp i
    have hi : s.factor p i ∈ s.selectedFactors := (s.mem_selectedFactors _).mpr ⟨p, hp, i, rfl⟩
    exact hz (s.factor p i) hi (s.selectedFactor_nonunit hi)
  · intro hz t ht _hunit
    obtain ⟨p, hp, i, rfl⟩ := (s.mem_selectedFactors t).mp ht
    exact hz p hp i

theorem SplitSieve.avoiding_periodic (s : SplitSieve K) :
    ∀ z ∈ s.avoiding, ∀ v : 𝓞 K, z + (s.period : 𝓞 K) * v ∈ s.avoiding :=
  integerAvoidingSelectedDivisors_periodic (s.selectedFactors : Set (𝓞 K)) s.period
    (fun _ ht _ => s.selectedFactor_dvd_period ht)

end QuadraticMoat
