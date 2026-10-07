import QuadraticMoat.SignedSieve
import QuadraticMoat.PlanarContext

/-! Random signed-factor region estimates on native algebraic integers. -/
namespace QuadraticMoat
open NumberField MeasureTheory ProbabilityTheory
open OAI.GaussianMoat
open scoped Classical NNReal
variable {K : Type*} [Field K] [NumberField K]
variable {b : Module.Basis (Fin 2) ℤ (𝓞 K)}

noncomputable def SplitSieve.extendSigns (s : SplitSieve K) (σ : s.primes → Bool) (p : ℕ) : Bool := by
  classical
  exact if hp : p ∈ s.primes then σ ⟨p,hp⟩ else false

@[simp] theorem SplitSieve.extendSigns_mem (s : SplitSieve K) (σ : s.primes → Bool)
    (p : ℕ) (hp : p ∈ s.primes) : s.extendSigns σ p = σ ⟨p,hp⟩ := by
  simp [SplitSieve.extendSigns, hp]

noncomputable def SplitSieve.signedProduct (s : SplitSieve K) (σ : s.primes → Bool) : 𝓞 K :=
  ∏ p ∈ s.primes, signedFactor (s.factor p) (s.extendSigns σ p)

theorem SplitSieve.signedProduct_norm (s : SplitSieve K) (σ : s.primes → Bool) :
    integerAbsNorm K (s.signedProduct σ) = s.period := by
  unfold SplitSieve.signedProduct SplitSieve.period
  rw [map_prod]
  exact Finset.prod_congr rfl (fun p hp => s.signedFactor_norm p hp _)

theorem SplitSieve.signedProduct_ne_zero (s : SplitSieve K) (σ : s.primes → Bool) :
    s.signedProduct σ ≠ 0 := by
  intro h
  have hn : integerAbsNorm K (s.signedProduct σ) = 0 := (integerAbsNorm_eq_zero _).mpr h
  rw [s.signedProduct_norm] at hn
  exact (Nat.ne_of_gt s.period_pos) hn

theorem SplitSieve.line_witness_log_lower (s : SplitSieve K) (σ : s.primes → Bool)
    {v w : 𝓞 K} (hv : CoordinatePrimitive b v) (hv0 : v ≠ 0) (hw : w ≠ 0)
    (hline : basisDet b v w = 0) (hdiv : s.signedProduct σ ∣ w)
    {B : ℝ} (hbound : (integerAbsNorm K w : ℝ) ≤ B) :
    Real.log (integerAbsNorm K v : ℝ) / 2 + (∑ p : s.primes, Real.log (p : ℝ)) - Real.log B / 2 ≤
      ∑ p : s.primes, s.lineLog v p (σ p) := by
  classical
  let t := s.primes.filter (fun p => ¬signedFactor (s.factor p) (s.extendSigns σ p) ∣ v)
  have hp (p : ℕ) (hp : p ∈ t) : 0 < (p : ℝ) := by
    exact_mod_cast (s.prime_mem p (Finset.mem_filter.mp hp).1).pos
  have hprod : 0 < ∏ p ∈ t, (p : ℝ) := Finset.prod_pos hp
  have hvpos : 0 < (integerAbsNorm K v : ℝ) := by exact_mod_cast (integerAbsNorm_pos hv0)
  have hlo := s.line_witness_norm_lower b s.primes (fun _ h => h) (s.extendSigns σ) hv hw hline hdiv
  have hlow : (integerAbsNorm K v : ℝ) * (∏ p ∈ t, (p : ℝ))^2 ≤ B := by
    apply le_trans ?_ hbound
    have hc : (((integerAbsNorm K v : ℤ) * (∏ p ∈ t, (p : ℤ))^2 : ℤ) : ℝ) ≤ (integerAbsNorm K w : ℝ) := by exact_mod_cast hlo
    push_cast at hc
    exact hc
  have hlog := Real.log_le_log (mul_pos hvpos (sq_pos_of_pos hprod)) hlow
  rw [Real.log_mul hvpos.ne' (sq_pos_of_pos hprod).ne', Real.log_pow,
    Real.log_prod (fun p hp' => (hp p hp').ne')] at hlog
  have hsum : (∑ p ∈ t, Real.log (p : ℝ)) =
      (∑ p : s.primes, Real.log (p : ℝ)) - ∑ p : s.primes, s.lineLog v p (σ p) := by
    calc
      _ = ∑ p ∈ s.primes, (Real.log (p : ℝ) - s.lineLog v p (s.extendSigns σ p)) := by
        unfold t
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp'
        unfold SplitSieve.lineLog
        split_ifs <;> simp_all
      _ = _ := by
        rw [← Finset.sum_coe_sort s.primes
          (fun p => Real.log (p : ℝ) - s.lineLog v p (s.extendSigns σ p))]
        simp [SplitSieve.extendSigns, Finset.sum_sub_distrib]
  rw [hsum] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]

def SplitSieve.lineEvent (s : SplitSieve K) (Q : Set (𝓞 K)) (v : 𝓞 K)
    (σ : s.primes → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ basisDet b v w = 0 ∧ s.signedProduct σ ∣ w

theorem SplitSieve.line_event_tail (s : SplitSieve K) {Q : Set (𝓞 K)}
    {v : 𝓞 K} (hv : CoordinatePrimitive b v) (hv0 : v ≠ 0) {B ε : ℝ}
    (hQ : ∀ w ∈ Q, (integerAbsNorm K w : ℝ) ≤ B) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : s.primes, Real.log (p : ℝ)) - Real.log B / 2) :
    (signMeasure s.primes).real {σ | s.lineEvent (b := b) Q v σ} ≤
      Real.exp (-ε^2 / (2 * ∑ p : s.primes,
        (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) := by
  apply le_trans (measureReal_mono (s₂ := {σ |
    Real.log (integerAbsNorm K v : ℝ) / 2 + ε ≤ ∑ p : s.primes, s.lineLog v p (σ p)}) ?_)
  · exact s.lineLog_tail b hv hv0 hε
  · rintro σ ⟨w,hwQ,hw,hline,hd⟩
    have hl := s.line_witness_log_lower (b := b) σ hv hv0 hw hline hd (hQ w hwQ)
    change Real.log (integerAbsNorm K v : ℝ) / 2 + ε ≤ _
    linarith

open scoped Classical in

noncomputable def SplitSieve.commonProduct (s : SplitSieve K) (σ τ : s.primes → Bool) : 𝓞 K :=
  ∏ p ∈ s.primes.filter (fun p => s.extendSigns σ p = s.extendSigns τ p),
    signedFactor (s.factor p) (s.extendSigns σ p)

theorem SplitSieve.commonProduct_dvd_left (s : SplitSieve K) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ ∣ s.signedProduct σ := by
  classical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem SplitSieve.commonProduct_comm (s : SplitSieve K) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ = s.commonProduct τ σ := by
  classical
  unfold SplitSieve.commonProduct
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, eq_comm]
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]

theorem SplitSieve.commonProduct_dvd_right (s : SplitSieve K) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ ∣ s.signedProduct τ := by
  rw [s.commonProduct_comm]
  exact s.commonProduct_dvd_left τ σ

open scoped Classical in
theorem SplitSieve.signDist_eq_card (s : SplitSieve K) (σ τ : s.primes → Bool) :
    signDist σ τ = (s.primes.filter (fun p => s.extendSigns σ p ≠ s.extendSigns τ p)).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_coe_sort s.primes
    (fun p => if s.extendSigns σ p ≠ s.extendSigns τ p then 1 else 0)]
  unfold signDist
  apply Finset.sum_congr rfl
  intro p _
  simp [SplitSieve.extendSigns]

theorem SplitSieve.period_le_common_norm (s : SplitSieve K) (σ τ : s.primes → Bool)
    {U : ℝ} (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U) :
    (s.period : ℝ) ≤ (integerAbsNorm K (s.commonProduct σ τ) : ℝ) * U^(signDist σ τ) := by
  classical
  let c := s.primes.filter (fun p => s.extendSigns σ p = s.extendSigns τ p)
  let d := s.primes.filter (fun p => s.extendSigns σ p ≠ s.extendSigns τ p)
  have hc : (integerAbsNorm K (s.commonProduct σ τ) : ℝ) = ∏ p ∈ c, (p : ℝ) := by
    unfold SplitSieve.commonProduct
    rw [map_prod, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [s.signedFactor_norm p (Finset.mem_filter.mp hp).1]
  have hd : (∏ p ∈ d, (p : ℝ)) ≤ U^d.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
      (fun p hp => hpU p (Finset.mem_filter.mp hp).1)
  have hp : (s.period : ℝ) = (∏ p ∈ c, (p : ℝ)) * (∏ p ∈ d, (p : ℝ)) := by
    unfold SplitSieve.period
    push_cast
    exact (Finset.prod_filter_mul_prod_filter_not s.primes
      (fun p => s.extendSigns σ p = s.extendSigns τ p) (fun p => (p : ℝ))).symm
  rw [hp, hc, s.signDist_eq_card]
  exact mul_le_mul_of_nonneg_left hd (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p))

theorem SplitSieve.near_witnesses_collinear (s : SplitSieve K) (σ τ : s.primes → Bool)
    {w w' : 𝓞 K} (hw : s.signedProduct σ ∣ w) (hw' : s.signedProduct τ ∣ w')
    {U B : ℝ} (hU : 0 < U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hdet : (|basisDet b w w'| : ℝ) ≤ B)
    (hsmall : B * U^(signDist σ τ) < (s.period : ℝ)) : basisDet b w w' = 0 := by
  have hbound := lt_of_lt_of_le hsmall (s.period_le_common_norm σ τ hpU)
  have hlt : B < (integerAbsNorm K (s.commonProduct σ τ) : ℝ) :=
    (mul_lt_mul_iff_left₀ (pow_pos hU _)).mp (by simpa only [mul_comm] using hbound)
  apply basisDet_eq_zero_of_common_factor b
    ((s.commonProduct_dvd_left σ τ).trans hw) ((s.commonProduct_dvd_right σ τ).trans hw')
  have hlt' : (|basisDet b w w'| : ℝ) < (|Algebra.norm ℤ (s.commonProduct σ τ)| : ℝ) := by
    simpa only [integerAbsNorm_apply, Nat.cast_natAbs, Int.cast_abs] using hdet.trans_lt hlt
  exact_mod_cast hlt'

omit [NumberField K] in
theorem basisDet_zero_trans {u v w : 𝓞 K} (hv : v ≠ 0)
    (huv : basisDet b u v = 0) (hvw : basisDet b v w = 0) : basisDet b u w = 0 := by
  rw [basisDet_eq_coordinate_determinant] at huv hvw ⊢
  apply OAI.GaussianMoat.determinant_zero_trans (v := coordinateGaussian b v) ?_ huv hvw
  intro h
  exact hv ((coordinateGaussian b).injective (by simpa only [map_zero] using h))

omit [NumberField K] in
@[simp] theorem basisDet_self (v : 𝓞 K) : basisDet b v v = 0 := by
  unfold basisDet
  ring

omit [NumberField K] in
theorem basisDet_swap (u v : 𝓞 K) : basisDet b u v = -basisDet b v u := by
  unfold basisDet
  ring

def witnessLine (v : 𝓞 K) : Set (𝓞 K) := {w | basisDet b v w = 0}

omit [NumberField K] in
theorem witnessLine_eq {v w : 𝓞 K} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : basisDet b v w = 0) : witnessLine (b := b) v = witnessLine (b := b) w := by
  ext u
  constructor
  · intro hu
    exact basisDet_zero_trans hv (by rw [basisDet_swap, hvw, neg_zero]) hu
  · exact basisDet_zero_trans hw hvw

def SplitSieve.badSign (s : SplitSieve K) (Q : Set (𝓞 K)) (σ : s.primes → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ s.signedProduct σ ∣ w

noncomputable def SplitSieve.badWitness (s : SplitSieve K) (Q : Set (𝓞 K))
    (σ : {σ : s.primes → Bool // s.badSign Q σ}) : 𝓞 K := σ.property.choose

theorem SplitSieve.badWitness_spec (s : SplitSieve K) (Q : Set (𝓞 K))
    (σ : {σ : s.primes → Bool // s.badSign Q σ}) :
    s.badWitness Q σ ∈ Q ∧ s.badWitness Q σ ≠ 0 ∧ s.signedProduct σ.val ∣ s.badWitness Q σ :=
  σ.property.choose_spec

def SplitSieve.badLines (s : SplitSieve K) (Q : Set (𝓞 K)) : Set (Set (𝓞 K)) :=
  Set.range (fun σ : {σ : s.primes → Bool // s.badSign Q σ} => witnessLine (b := b) (s.badWitness Q σ))

instance SplitSieve.badLines_finite (s : SplitSieve K) (Q : Set (𝓞 K)) :
    Finite (s.badLines (b := b) Q) := by
  unfold SplitSieve.badLines
  infer_instance

theorem SplitSieve.badLine_primitive (s : SplitSieve K) (Q : Set (𝓞 K))
    (L : s.badLines (b := b) Q) : ∃ v : 𝓞 K, CoordinatePrimitive b v ∧ v ≠ 0 ∧ witnessLine (b := b) v = L.val := by
  obtain ⟨σ, hσ⟩ := L.property
  have hw := s.badWitness_spec Q σ
  obtain ⟨v,hv,hv0,a,_hanz,ha⟩ := exists_coordinate_primitive_direction b hw.2.1
  refine ⟨v,hv,hv0, ?_⟩
  rw [← hσ]
  apply witnessLine_eq (b := b) hv0 hw.2.1
  rw [ha]
  have hf : b.repr ((a : 𝓞 K) * v) = a • b.repr v := by
    simpa only [Algebra.smul_def, algebraMap_int_eq, Int.coe_castRingHom] using b.repr.map_smul a v
  unfold basisDet
  rw [hf]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  ring

def SplitSieve.lineClass (s : SplitSieve K) (Q : Set (𝓞 K)) (L : s.badLines (b := b) Q)
    (σ : s.primes → Bool) : Prop :=
  ∃ hσ : s.badSign Q σ, witnessLine (b := b) (s.badWitness Q ⟨σ,hσ⟩) = L.val

theorem SplitSieve.badSign_iff_class (s : SplitSieve K) (Q : Set (𝓞 K)) (σ : s.primes → Bool) :
    s.badSign Q σ ↔ ∃ L : s.badLines (b := b) Q, s.lineClass (b := b) Q L σ := by
  constructor
  · intro hσ
    exact ⟨⟨witnessLine (b := b) (s.badWitness Q ⟨σ,hσ⟩), ⟨⟨σ,hσ⟩,rfl⟩⟩, hσ, rfl⟩
  · rintro ⟨L,hσ,_⟩
    exact hσ

theorem SplitSieve.lineClass_subset_event (s : SplitSieve K) (Q : Set (𝓞 K))
    (L : s.badLines (b := b) Q) {v : 𝓞 K} (hvL : witnessLine (b := b) v = L.val) :
    {σ | s.lineClass (b := b) Q L σ} ⊆ {σ | s.lineEvent (b := b) Q v σ} := by
  rintro σ ⟨hσ,hL⟩
  have hw := s.badWitness_spec Q ⟨σ,hσ⟩
  refine ⟨_,hw.1,hw.2.1,?_,hw.2.2⟩
  change s.badWitness Q ⟨σ,hσ⟩ ∈ witnessLine (b := b) v
  rw [hvL, ← hL]
  exact basisDet_self _

theorem SplitSieve.lineClasses_separated (s : SplitSieve K) (Q : Set (𝓞 K))
    {U B : ℝ} (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, (|basisDet b w w'| : ℝ) ≤ B)
    {h : ℕ} (hsmall : B * U^(2*h) < (s.period : ℝ)) (hB : 0 ≤ B) :
    ∀ L L' : s.badLines (b := b) Q, L ≠ L' → ∀ σ, s.lineClass (b := b) Q L σ →
      ∀ τ, s.lineClass (b := b) Q L' τ → 2*h < signDist σ τ := by
  intro L L' hLL σ ⟨hσ,hσL⟩ τ ⟨hτ,hτL⟩
  by_contra hn
  have hd : signDist σ τ ≤ 2*h := le_of_not_gt hn
  have hw := s.badWitness_spec Q ⟨σ,hσ⟩
  have hw' := s.badWitness_spec Q ⟨τ,hτ⟩
  have hsm : B * U^(signDist σ τ) < (s.period : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU hd) hB).trans_lt hsmall
  have hcol := s.near_witnesses_collinear (b := b) σ τ hw.2.2 hw'.2.2 (by linarith) hpU
    (hdet _ hw.1 _ hw'.1) hsm
  apply hLL
  apply Subtype.ext
  rw [← hσL, ← hτL]
  exact witnessLine_eq (b := b) hw.2.1 hw'.2.1 hcol

theorem SplitSieve.signed_region_bound (s : SplitSieve K) (Q : Set (𝓞 K))
    (hr : 0 < s.primes.card) {U B N ε a E A : ℝ} {h : ℕ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hB : 0 ≤ B) (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, (|basisDet b w w'| : ℝ) ≤ B)
    (hsmall : B * U^(2*h) < (s.period : ℝ))
    (hQ : ∀ w ∈ Q, (integerAbsNorm K w : ℝ) ≤ N) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : s.primes, Real.log (p : ℝ)) - Real.log N / 2)
    (ha : 0 ≤ a) (hE : 0 < E) (hA : 0 < A)
    (hlogE : Real.log E ≤ (s.primes.card : ℝ) * Real.log 2 - a)
    (hseed : A * Real.exp (-ε^2 / (2 * ∑ p : s.primes,
      (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) * (2 : ℝ)^s.primes.card ≤ E)
    (hfactor : A ≤ (1 + a / ((s.primes.card : ℝ)*Real.log 2))^h) :
    (signMeasure s.primes).real {σ | s.badSign Q σ} ≤ A⁻¹ := by
  classical
  let : Fintype (s.badLines (b := b) Q) := Fintype.ofFinite _
  let S : s.badLines (b := b) Q → Cube (Fintype.card s.primes) → Prop :=
    fun L x => s.lineClass (b := b) Q L (cubeSignEquiv s.primes x)
  have hcard : Fintype.card s.primes = s.primes.card := Fintype.card_coe _
  have hpow : 0 < (2 : ℝ)^Fintype.card s.primes := pow_pos (by norm_num) _
  have hseed' (L : s.badLines (b := b) Q) : A * cubeSize (S L) ≤ E := by
    obtain ⟨v,hv,hv0,hvL⟩ := s.badLine_primitive (b := b) Q L
    have hm := (measureReal_mono (s.lineClass_subset_event (b := b) Q L hvL)).trans
      (s.line_event_tail (b := b) hv hv0 hQ hε hexcess)
    rw [cubeSignEquiv_measure] at hm
    have hc : (cubeSize (S L) : ℝ) ≤ Real.exp (-ε^2 / (2 * ∑ p : s.primes,
        (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) * (2 : ℝ)^Fintype.card s.primes :=
      (div_le_iff₀ hpow).mp hm
    have hh := mul_le_mul_of_nonneg_left hc hA.le
    exact hh.trans (by simpa only [hcard, mul_assoc] using hseed)
  have hsep : ∀ L L' : s.badLines (b := b) Q, L ≠ L' → ∀ x, S L x → ∀ y, S L' y →
      2*h < cubeDist (Fintype.card s.primes) x y := by
    intro L L' hLL x hx y hy
    have hh := s.lineClasses_separated (b := b) Q hU hpU hdet hsmall hB L L' hLL
      (cubeSignEquiv s.primes x) hx (cubeSignEquiv s.primes y) hy
    simpa only [cubeSignEquiv_dist] using hh
  have hpack := cube_separated_bound (n := Fintype.card s.primes) (h := h)
    (by simpa only [hcard] using hr) S ha hE (by simpa only [hcard] using hlogE)
    hseed' (by simpa only [hcard] using hfactor) hsep
  have hunion : (cubeSize (fun x => s.badSign Q (cubeSignEquiv s.primes x)) : ℝ) ≤
      ∑ L, (cubeSize (S L) : ℝ) := by
    have he : (fun x => s.badSign Q (cubeSignEquiv s.primes x)) = (fun x => ∃ L, S L x) := by
      funext x
      exact propext (s.badSign_iff_class (b := b) Q _)
    rw [he]
    exact_mod_cast cubeSize_exists_le_sum S
  rw [cubeSignEquiv_measure, div_le_iff₀ hpow]
  have hh := (mul_le_mul_of_nonneg_left hunion hA.le).trans hpack
  calc
    _ ≤ (2 : ℝ)^Fintype.card s.primes / A := (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

theorem SplitSieve.signed_region_exp_bound (s : SplitSieve K) (Q : Set (𝓞 K))
    (hr : 0 < s.primes.card) {U B N ε a β : ℝ} {h : ℕ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hB : 0 ≤ B) (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, (|basisDet b w w'| : ℝ) ≤ B)
    (hsmall : B * U^(2*h) < (s.period : ℝ))
    (hQ : ∀ w ∈ Q, (integerAbsNorm K w : ℝ) ≤ N) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : s.primes, Real.log (p : ℝ)) - Real.log N / 2)
    (ha : 0 ≤ a) (hb : β ≤ a)
    (htail : 2*a ≤ ε^2 / (2 * ∑ p : s.primes,
      (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)))
    (hgrowth : β ≤ (h : ℝ) * Real.log (1 + a / ((s.primes.card : ℝ)*Real.log 2))) :
    (signMeasure s.primes).real {σ | s.badSign Q σ} ≤ Real.exp (-β) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr' : 0 < (s.primes.card : ℝ) := by exact_mod_cast hr
  have hbase : 0 < 1 + a / ((s.primes.card : ℝ)*Real.log 2) := by
    have := div_nonneg ha (mul_pos hr' htwo).le
    linarith
  have hbexp : Real.exp β ≤ (1 + a / ((s.primes.card : ℝ)*Real.log 2))^h := by
    rw [← Real.exp_log (pow_pos hbase h)]
    apply Real.exp_le_exp.mpr
    simpa only [Real.log_pow] using hgrowth
  have hh := s.signed_region_bound (b := b) Q hr hU hpU hB hdet hsmall hQ hε hexcess ha
    (E := (2 : ℝ)^s.primes.card * Real.exp (-a))
    (A := Real.exp β) (h := h) (mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _))
    (Real.exp_pos _) (by
      rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' (Real.exp_pos _).ne',
        Real.log_pow, Real.log_exp]
      linarith) (by
      rw [← Real.exp_add]
      have he : β + -ε^2 / (2 * ∑ p : s.primes,
          (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)) ≤ -a := by
        rw [neg_div]
        linarith
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg (by norm_num) _)).trans_eq (mul_comm _ _)) hbexp
  simpa only [Real.exp_neg] using hh


/-- The symmetric rectangle in the scaled auxiliary planar coordinates. -/
def orientedRectangle (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (scale : ℝ)
    (e : ℂ) (R W : ℝ) : Set (𝓞 K) :=
  {z | |(star e * scaledCoordinateComplex b scale z).re| ≤ R ∧
    |(star e * scaledCoordinateComplex b scale z).im| ≤ W}

theorem scaled_rectangle_norm_bound (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (scale : ℝ)
    (hnorm : ∀ z : 𝓞 K, (integerAbsNorm K z : ℝ) ≤ ‖scaledCoordinateComplex b scale z‖ ^ 2)
    {e : ℂ} (he : ‖e‖ = 1) {R W : ℝ} (hW : 0 ≤ W) (hWR : W ≤ R)
    {z : 𝓞 K} (hz : z ∈ orientedRectangle b scale e R W) :
    (integerAbsNorm K z : ℝ) ≤ 2 * R ^ 2 := by
  apply (hnorm z).trans
  have hrot : ‖star e * scaledCoordinateComplex b scale z‖ = ‖scaledCoordinateComplex b scale z‖ := by
    rw [norm_mul, norm_star, he, one_mul]
  rw [← hrot, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hx : (star e * scaledCoordinateComplex b scale z).re ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hW.trans hWR)).mpr hz.1
  have hy : (star e * scaledCoordinateComplex b scale z).im ^ 2 ≤ W ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hW).mpr hz.2
  have hww := (sq_le_sq₀ hW (hW.trans hWR)).mpr hWR
  nlinarith

private theorem complex_determinant_rotated (e : ℂ) (he : ‖e‖ = 1) (z w : ℂ) :
    z.re * w.im - z.im * w.re =
      (star e * z).re * (star e * w).im - (star e * z).im * (star e * w).re := by
  have hsq : e.re ^ 2 + e.im ^ 2 = 1 := by
    have hh := Complex.normSq_eq_norm_sq e
    rw [he] at hh
    simpa [Complex.normSq_apply, pow_two] using hh
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [congrArg (fun x : ℝ => x * (z.re * w.im - z.im * w.re)) hsq]

omit [NumberField K] in
theorem scaled_rectangle_determinant_bound (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    (scale : ℝ) (hscale : 1 ≤ scale) {e : ℂ} (he : ‖e‖ = 1) {R W : ℝ}
    (hR : 0 ≤ R) (hW : 0 ≤ W) {z w : 𝓞 K}
    (hz : z ∈ orientedRectangle b scale e R W) (hw : w ∈ orientedRectangle b scale e R W) :
    (|basisDet b z w| : ℝ) ≤ 2 * R * W := by
  have hscaled : scale ^ 2 * (basisDet b z w : ℝ) =
      (star e * scaledCoordinateComplex b scale z).re * (star e * scaledCoordinateComplex b scale w).im -
      (star e * scaledCoordinateComplex b scale z).im * (star e * scaledCoordinateComplex b scale w).re := by
    rw [basisDet_eq_coordinate_determinant]
    unfold OAI.GaussianMoat.determinant
    rw [← scaled_coordinate_determinant]
    exact complex_determinant_rotated e he _ _
  have hphys : |(star e * scaledCoordinateComplex b scale z).re * (star e * scaledCoordinateComplex b scale w).im -
      (star e * scaledCoordinateComplex b scale z).im * (star e * scaledCoordinateComplex b scale w).re| ≤
      2 * R * W := by
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul hz.1 hw.2 (abs_nonneg _) hR
    have h2 := mul_le_mul hz.2 hw.1 (abs_nonneg _) hW
    nlinarith
  rw [← hscaled, abs_mul, abs_of_nonneg (sq_nonneg scale)] at hphys
  have hsq : 1 ≤ scale ^ 2 := by nlinarith
  have hle : |(basisDet b z w : ℝ)| ≤ scale ^ 2 * |(basisDet b z w : ℝ)| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (abs_nonneg (basisDet b z w : ℝ))
  exact hle.trans hphys

theorem SplitSieve.log_period (s : SplitSieve K) :
    Real.log (s.period : ℝ) = ∑ p : s.primes, Real.log (p : ℝ) := by
  classical
  unfold SplitSieve.period
  push_cast
  rw [Real.log_prod (fun p hp => by
    exact_mod_cast (s.prime_mem p hp).ne_zero)]
  exact (Finset.sum_coe_sort s.primes (fun p => Real.log (p : ℝ))).symm

noncomputable def SplitSieve.logVariance (s : SplitSieve K) : ℝ :=
  ∑ p : s.primes, (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)

theorem SplitSieve.logVariance_pos (s : SplitSieve K) (hr : 0 < s.primes.card) :
    0 < s.logVariance := by
  classical
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hr
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (s.prime_mem p hp).one_lt)
  apply Finset.sum_pos' (fun _ _ => by positivity)
  refine ⟨⟨p,hp⟩, Finset.mem_univ _, ?_⟩
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos hlog]
  positivity

theorem SplitSieve.logVariance_le (s : SplitSieve K) {U : ℝ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U) :
    s.logVariance ≤ (s.primes.card : ℝ) * (Real.log U / 2)^2 := by
  classical
  calc
    _ ≤ ∑ _p : s.primes, (Real.log U / 2)^2 := by
      apply Finset.sum_le_sum
      intro p _
      have hp : 0 < (p : ℝ) := by exact_mod_cast (s.prime_mem p p.property).pos
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (s.prime_mem p p.property).one_le)
      have hle := Real.log_le_log hp (hpU p p.property)
      simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg hlog]
      exact (sq_le_sq₀ (by positivity) (div_nonneg (Real.log_nonneg hU) (by norm_num))).mpr (by linarith)
    _ = _ := by simp [nsmul_eq_mul]

theorem SplitSieve.signed_rectangle (s : SplitSieve K)
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (scale : ℝ) (hscale : 1 ≤ scale)
    (hnorm : ∀ z : 𝓞 K, (integerAbsNorm K z : ℝ) ≤ ‖scaledCoordinateComplex b scale z‖ ^ 2)
    {T R W d : ℝ} {e : ℂ} (he : ‖e‖ = 1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (harea : R*W ≤ (s.period : ℝ)^(1-d)) (hlarge : 1000 ≤ d^3*s.primes.card) :
    (signMeasure s.primes).real {σ | s.badSign (orientedRectangle b scale e R W) σ} ≤
      Real.exp (-(d^3*s.primes.card/5120)) := by
  have hr : 0 < s.primes.card := by
    by_contra h
    have hz : s.primes.card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hr' : 0 < (s.primes.card : ℝ) := by exact_mod_cast hr
  have hP : 0 < (s.period : ℝ) := by exact_mod_cast s.period_pos
  have hTpos : 0 < T := by linarith
  have hU : 1 ≤ 2*T := by linarith
  have hUpos : 0 < 2*T := by linarith
  have hWpos : 0 < W := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le hWpos hWR
  have hRW : 0 < R*W := mul_pos hRpos hWpos
  have hlogT : 1/2 ≤ Real.log T := by
    have hlog2T := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ T)
    linarith [Real.log_two_gt_d9]
  have hlogU : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ T)
    linarith
  have hlogP : (s.primes.card : ℝ)*Real.log T ≤ Real.log (s.period : ℝ) := by
    rw [s.log_period]
    calc
      _ = ∑ _p : s.primes, Real.log T := by simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun p _ => Real.log_le_log hTpos (hpT p p.property).1)
  have hlogPpos : 0 < Real.log (s.period : ℝ) :=
    (mul_pos hr' (by linarith : 0 < Real.log T)).trans_le hlogP
  have hRarea : R ≤ R*W := by nlinarith
  have hlogR : Real.log R ≤ (1-d)*Real.log (s.period : ℝ) := by
    have hh := Real.log_le_log hRpos (hRarea.trans harea)
    simpa only [Real.log_rpow hP] using hh
  have hlogB : Real.log (2*R*W) ≤ Real.log 2 + (1-d)*Real.log (s.period : ℝ) := by
    have hh := Real.log_le_log hRW harea
    rw [Real.log_rpow hP] at hh
    have heq : 2*R*W = 2*(R*W) := by ring
    rw [heq, Real.log_mul (by norm_num) hRW.ne']
    linarith
  have hlogN : Real.log (2*R^2)/2 ≤ (1-d)*Real.log (s.period : ℝ) + Real.log 2/2 := by
    rw [Real.log_mul (by norm_num) (pow_pos hRpos 2).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  let h : ℕ := ⌊d*s.primes.card/10⌋₊
  have hsmall : (2*R*W) * (2*T)^(2*h) < (s.period : ℝ) := by
    apply (Real.log_lt_log_iff (mul_pos (by positivity) (pow_pos hUpos _)) hP).mp
    rw [Real.log_mul (by positivity : 2*R*W ≠ 0) (pow_pos hUpos _).ne', Real.log_pow]
    have hh := rectangle_log_small hd hd1.le hlogT (Real.log_nonneg hU) hlogU hlogP hlarge
    exact (add_le_add_left hlogB _).trans_lt hh
  have hV := s.logVariance_pos hr
  have hVup : s.logVariance ≤ (s.primes.card : ℝ)*(Real.log T)^2 := by
    apply (s.logVariance_le hU (fun p hp => (hpT p hp).2)).trans
    apply mul_le_mul_of_nonneg_left ?_ hr'.le
    apply (sq_le_sq₀ (div_nonneg (Real.log_nonneg hU) (by norm_num)) (by linarith : 0 ≤ Real.log T)).mpr
    linarith
  apply s.signed_region_exp_bound (b := b) (orientedRectangle b scale e R W) hr hU
    (fun p hp => (hpT p hp).2) (by positivity) (fun _ hw _ hw' =>
      scaled_rectangle_determinant_bound b scale hscale he hRpos.le hWpos.le hw hw') hsmall
    (fun _ hz => scaled_rectangle_norm_bound b scale hnorm he hWpos.le hWR hz)
    (ε := d*Real.log (s.period : ℝ)/2) (a := d^2*s.primes.card/64) (h := h)
  · positivity
  · rw [← s.log_period]
    have hh := rectangle_log_excess hd hd1.le hlogT hlogP hlarge
    linarith
  · positivity
  · have hc : d^3 ≤ d^2 := by nlinarith [sq_nonneg d, mul_nonneg (sq_nonneg d) (by linarith : 0 ≤ 1-d)]
    have hh := mul_le_mul_of_nonneg_right hc hr'.le
    nlinarith [mul_nonneg (sq_nonneg d) hr'.le]
  · exact rectangle_hoeffding_exponent hr' hd.le (by linarith) hlogP hV hVup
  · exact rectangle_cube_growth hd hd1.le hlarge

/-- The signed rectangle estimate specialized to the proved planar context data. -/
theorem SplitSieve.signed_rectangle_of_planarContext (s : SplitSieve K) (P : PlanarContext K)
    {T R W d : ℝ} {e : ℂ} (he : ‖e‖ = 1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1 / 4)
    (harea : R * W ≤ (s.period : ℝ) ^ (1 - d))
    (hlarge : 1000 ≤ d ^ 3 * s.primes.card) :
    (signMeasure s.primes).real {σ |
      s.badSign (orientedRectangle P.basis P.scale e R W) σ} ≤
      Real.exp (-(d ^ 3 * s.primes.card / 5120)) :=
  s.signed_rectangle P.basis P.scale P.scale_ge_one P.norm_bound
    he hT hpT hW hWR hd hd1 harea hlarge

end QuadraticMoat
