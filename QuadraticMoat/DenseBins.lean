import OAI.NumberTheory.GaussianMoat.DenseBins
import OAI.NumberTheory.GaussianMoat.BatchCertificate

/-!
# Dense dyadic batches for arbitrary supplied families of rational primes

This port retains the original Gaussian scaffold's scale constants. Arithmetic
is confined to `PrimeFamily.good` and its quantitative window-mass field.
-/

namespace QuadraticMoat
open Filter Topology Finset
open scoped BigOperators
open OAI.GaussianMoat.PrimeLogMass (windowIndices mem_windowIndices)

noncomputable def primeWindow (good : ℕ → Prop) (X : ℝ) : Finset ℕ := by
  classical
  exact (windowIndices X).filter good

/-- A rational prime family with positive logarithmic mass in the fixed
exponential windows used by the sieve. -/
structure PrimeFamily where
  good : ℕ → Prop
  prime_of_good : ∀ p, good p → p.Prime
  window_mass : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
    c*X ≤ ∑ p ∈ primeWindow good X, Real.log p/p

namespace PrimeFamily
variable (F : PrimeFamily)

noncomputable def dyadicBatch (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2^j) (2^(j+1))).filter (fun p => p.Prime ∧ F.good p)

lemma mem_dyadicBatch (j p : ℕ) : p ∈ dyadicBatch F j ↔
    2^j ≤ p ∧ p < 2^(j+1) ∧ p.Prime ∧ F.good p := by
  classical
  simp only [dyadicBatch,Finset.mem_filter,Finset.mem_Ico]
  tauto

lemma logBin_mem (p : ℕ) (hp : p.Prime) (hm : F.good p) :
    p ∈ dyadicBatch F (Nat.log 2 p) := by
  rw [mem_dyadicBatch F]
  exact ⟨Nat.pow_log_le_self 2 hp.ne_zero,
    Nat.lt_pow_succ_log_self (by norm_num) p,hp,hm⟩

noncomputable def dyadicMass (j : ℕ) : ℝ :=
  ∑ p ∈ dyadicBatch F j, Real.log p/p

lemma dyadicMass_nonneg (j : ℕ) : 0 ≤ dyadicMass F j := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (mem_dyadicBatch F _ _ |>.mp hp).2.2.1.one_le))
    (Nat.cast_nonneg _)

lemma dyadicMass_le (j : ℕ) : dyadicMass F j ≤ 2*Real.log 4 := by
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hs : dyadicMass F j ≤ (∑ p ∈ dyadicBatch F j, Real.log p)/(2^j : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have h := (mem_dyadicBatch F j p).mp hp
    apply div_le_div_of_nonneg_left
    · exact Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)
    · exact hT
    · exact_mod_cast h.1
  have ht := OAI.GaussianMoat.PrimeLogMass.prime_log_mass_le_theta (dyadicBatch F j) (U := (2 : ℝ)^(j+1))
    (by positivity) (by intro p hp; have h := (mem_dyadicBatch F j p).mp hp
                        exact ⟨h.2.2.1,by exact_mod_cast h.2.1.le⟩)
  apply hs.trans
  apply (div_le_iff₀ hT).mpr
  rw [pow_succ] at ht
  nlinarith

lemma dyadicMass_le_card (j : ℕ) : dyadicMass F j ≤
    (dyadicBatch F j).card * Real.log ((2 : ℝ)^(j+1)) / (2 : ℝ)^j := by
  rw [dyadicMass]
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hp (p : ℕ) (hp : p ∈ dyadicBatch F j) :
      Real.log p/p ≤ Real.log ((2 : ℝ)^(j+1))/(2 : ℝ)^j := by
    have h := (mem_dyadicBatch F j p).mp hp
    apply le_trans (div_le_div_of_nonneg_left
      (Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)) hT (by exact_mod_cast h.1))
    apply div_le_div_of_nonneg_right _ hT.le
    exact Real.log_le_log (by exact_mod_cast h.2.2.1.pos) (by exact_mod_cast h.2.1.le)
  have hs := Finset.sum_le_sum (s := dyadicBatch F j) hp
  simpa [Finset.sum_const,nsmul_eq_mul,mul_div_assoc] using hs

theorem many_dense_bins (J : Finset ℕ) {X c A : ℝ} (hc : 0 < c)
    (hA : 0 < A) (hcard : (J.card : ℝ) ≤ A*X)
    (hmass : c*X ≤ ∑ j ∈ J, dyadicMass F j) :
    c*X/(4*Real.log 4) ≤
      ((J.filter (fun j => c/(2*A) ≤ dyadicMass F j)).card : ℝ) ∧
    ∀ j ∈ J.filter (fun j => c/(2*A) ≤ dyadicMass F j),
      c/(2*A)*(2 : ℝ)^j/Real.log ((2 : ℝ)^(j+1)) ≤ (dyadicBatch F j).card := by
  classical
  let G := J.filter (fun j => c/(2*A) ≤ dyadicMass F j)
  have hlog : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hδ : 0 < c/(2*A) := div_pos hc (by positivity)
  have ht (j : ℕ) (hj : j ∈ J) : dyadicMass F j ≤
      (if j ∈ G then 2*Real.log 4 else 0)+c/(2*A) := by
    by_cases hg : j ∈ G
    · simp only [hg,ite_eq_left]
      linarith [dyadicMass_le F j]
    · rw [ite_eq_right hg,zero_add]
      exact (not_le.mp (fun h => hg (Finset.mem_filter.mpr ⟨hj,h⟩))).le
  have hs := Finset.sum_le_sum (s := J) ht
  have he : (∑ j ∈ J, if j ∈ G then 2*Real.log 4 else 0) = G.card*(2*Real.log 4) := by
    rw [← Finset.sum_filter]
    have hG : J.filter (fun j => j ∈ G) = G := by
      ext j
      simp only [G,Finset.mem_filter]
      tauto
    rw [hG]
    simp [nsmul_eq_mul]
  rw [Finset.sum_add_distrib,he,Finset.sum_const,nsmul_eq_mul] at hs
  have hsmall : (J.card : ℝ)*(c/(2*A)) ≤ c*X/2 := by
    have h := mul_le_mul_of_nonneg_right hcard hδ.le
    have he : A*X*(c/(2*A))=c*X/2 := by field_simp
    rwa [he] at h
  refine ⟨(div_le_iff₀ (by positivity)).mpr (by dsimp [G] at hs; nlinarith),?_⟩
  intro j hj
  have hg := (Finset.mem_filter.mp hj).2
  have h := dyadicMass_le_card F j
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hL : 0 < Real.log ((2 : ℝ)^(j+1)) := Real.log_pos (one_lt_pow₀ (by norm_num) (by omega))
  apply (div_le_iff₀ hL).mpr
  have h' := (le_div_iff₀ hT).mp (hg.trans h)
  exact h'

noncomputable def splitWindow (X : ℝ) : Finset ℕ := by
  classical
  exact (windowIndices X).filter (fun p => p.Prime ∧ F.good p)

noncomputable def windowBins (X : ℝ) : Finset ℕ :=
  (splitWindow F X).image (Nat.log 2)

lemma splitWindow_eq_primeWindow (X : ℝ) : splitWindow F X = primeWindow F.good X := by
  classical
  ext p
  simp only [splitWindow, primeWindow, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, F.prime_of_good p h.2, h.2⟩

lemma window_mass_le_bins (X : ℝ) :
    (∑ p ∈ primeWindow F.good X, Real.log p/p) ≤
      ∑ j ∈ windowBins F X, dyadicMass F j := by
  classical
  rw [← splitWindow_eq_primeWindow F X, ← Finset.sum_fiberwise_of_maps_to
    (s := splitWindow F X) (t := windowBins F X) (g := Nat.log 2)
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)]
  apply Finset.sum_le_sum
  intro j _
  dsimp [dyadicMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hj⟩
    obtain ⟨_,hpp,hpm⟩ := Finset.mem_filter.mp hp
    rw [← hj]
    exact logBin_mem F p hpp hpm
  · intro p hp _
    have hpp := ((mem_dyadicBatch F j p).mp hp).2.2.1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg p)

lemma windowBin_bounds {X : ℝ} (hX : 1000 ≤ X) {j : ℕ} (hj : j ∈ windowBins F X) :
    X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X := by
  classical
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hpW,hpP,hpM⟩ := Finset.mem_filter.mp hp
  have hw := (mem_windowIndices X p).mp hpW
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
  have hlb := (Real.le_log_iff_exp_le hp0).mpr hw.1
  have hub := (Real.log_le_iff_le_exp hp0).mpr hw.2
  have hbin := (mem_dyadicBatch F _ _).mp (logBin_mem F p hpP hpM)
  have hlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) (Nat.log 2 p))
    (by exact_mod_cast hbin.1 : (2 : ℝ)^Nat.log 2 p ≤ p)
  have hhigh := Real.log_lt_log hp0
    (by exact_mod_cast hbin.2.1 : (p : ℝ) < (2 : ℝ)^(Nat.log 2 p+1))
  rw [Real.log_pow] at hlow hhigh
  simp only [Nat.cast_add,Nat.cast_one] at hhigh
  constructor
  · nlinarith [Real.log_two_lt_d9]
  · nlinarith

lemma windowBins_card {X : ℝ} (hX : 1000 ≤ X) : (windowBins F X).card ≤ 3*X := by
  classical
  have hX0 : 0 ≤ X := by linarith
  have hs : windowBins F X ⊆ Finset.range (⌊2*X⌋₊+1) := by
    intro j hj
    have h := (windowBin_bounds F hX hj).2
    have hlog := Real.log_two_gt_d9
    have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
    have hjX : (j : ℝ)≤2*X := by nlinarith
    rw [Finset.mem_range,Nat.lt_succ_iff,Nat.le_floor_iff (by positivity : (0 : ℝ)≤2*X)]
    exact hjX
  have hc : (windowBins F X).card ≤ ⌊2*X⌋₊+1 :=
    (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hcR : ((windowBins F X).card:ℝ) ≤ ⌊2*X⌋₊+1 := by exact_mod_cast hc
  have hf := Nat.floor_le (show (0 : ℝ)≤2*X by positivity)
  nlinarith

theorem eventually_dense_split_bins : ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      c*X ≤ J.card ∧
      ∀ j ∈ J, X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X ∧
        δ*(2 : ℝ)^j/Real.log ((2 : ℝ)^(j+1)) ≤ (dyadicBatch F j).card := by
  obtain ⟨c,hc,he⟩ := F.window_mass
  refine ⟨c/(4*Real.log 4),c/6,div_pos hc (by positivity),div_pos hc (by norm_num),?_⟩
  filter_upwards [he,eventually_ge_atTop (1000 : ℝ)] with X hmass hX
  let J := (windowBins F X).filter (fun j => c/6 ≤ dyadicMass F j)
  have hh := many_dense_bins F (windowBins F X) hc (by norm_num : (0 : ℝ)<3)
    (windowBins_card F hX) (hmass.trans (window_mass_le_bins F X))
  refine ⟨J,?_,?_⟩
  · simpa only [show (2 : ℝ)*3=6 by norm_num,div_mul_eq_mul_div] using hh.1
  · intro j hj
    have hb := windowBin_bounds F hX (Finset.mem_filter.mp hj).1
    have hd := hh.2 j (by simpa only [show (2 : ℝ)*3=6 by norm_num] using hj)
    exact ⟨hb.1,hb.2,by simpa only [show (2 : ℝ)*3=6 by norm_num] using hd⟩

/-- A positive proportion of supplied dense bins can be retained with any
prescribed positive gap between their indices. -/
theorem eventually_separated_split_bins (K : ℕ) (hK : 0 < K) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      c*X ≤ J.card ∧
      (∀ i ∈ J, ∀ j ∈ J, i < j → i+K ≤ j) ∧
      ∀ j ∈ J, X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X ∧
        δ*(2 : ℝ)^j/Real.log ((2 : ℝ)^(j+1)) ≤ (dyadicBatch F j).card := by
  classical
  obtain ⟨c,δ,hc,hδ,he⟩ := eventually_dense_split_bins F
  refine ⟨c/K,δ,div_pos hc (by exact_mod_cast hK),hδ,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩ := hX
  obtain ⟨a,_,hcard,hsep⟩ := OAI.GaussianMoat.thin_bins J hK
  refine ⟨J.filter (fun j => j%K=a),?_,hsep,?_⟩
  · have hh := (div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1

end PrimeFamily
end QuadraticMoat
