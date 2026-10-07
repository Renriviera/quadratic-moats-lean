import QuadraticMoat.Smoothing
import QuadraticMoat.WindowParameters
import OAI.NumberTheory.GaussianMoat.CommonBlocks

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
open Filter
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

lemma floor_size_lower {s : SplitSieve Fld} {g U X : ℝ} {l : ℕ}
    (hX : 0<X) (hm : 0<s.meanLog) (hm' : s.meanLog≤2*X)
    (hscale : Real.exp (X/8)≤bandScale g U l) (hlarge : 4*X≤Real.exp (X/8)) :
    Real.exp (X/8)/(4*X)≤(bandSize s g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/s.meanLog)
  have hh := mul_lt_mul_of_pos_right hf hm
  rw [div_mul_cancel₀ _ hm.ne',add_mul,one_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (bandSize s g U l))
  change (bandScale g U l)<((bandSize s g U l:ℝ)*s.meanLog)+s.meanLog at hh
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hf,hh,hb,hscale,hlarge,hm']

variable (F : PrimeFamily) (hgood : ∀ p, F.good p → Nonempty (SplitPrime Fld p))

theorem eventually_window_bands {D a δ : ℝ} (hD : 1≤D) (ha : 0≤a) (ha1 : a≤1)
    (hδ : 0<δ) (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, ((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(F.dyadicBatch j).card) →
      ∀ j∈J w,
        Nonempty (EntropyBand (F.dyadicSieve hgood j) D (middleBlocks a m w J) 0
          (bandSize (F.dyadicSieve hgood j) (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m))
          (91*accurateGrid m)) ∧
        Nonempty (EntropyBand (F.dyadicSieve hgood j) D (accurateBlock m (1/20)) (windowSmoothing W m)
          (bandSize (F.dyadicSieve hgood j) (accurateGrid m) (Real.exp ((1/20)*Real.exp m)) (accurateIterations m))
          (91*accurateGrid m)) ∧
        Real.exp (((100:ℝ)^w*Real.exp m)/8)/(4*((100:ℝ)^w*Real.exp m))≤
          (bandSize (F.dyadicSieve hgood j) (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m):ℝ) := by
  have hwp := window_power_one w
  have hp : (0:ℝ)<100^w := by positivity
  have hmid := eventually_accurate_band (Fld := Fld) (D := D) (A := (100:ℝ)^w) (B := 2*(100:ℝ)^w)
    (a := (100:ℝ)^w/4) (b := (100:ℝ)^w/50) hD hp (by positivity) (by linarith only [hp])
    (by linarith only [hp]) hδ
  have hbot := eventually_accurate_band (Fld := Fld) (D := D) (A := 1) (B := 2*(100:ℝ)^w)
    (a := 1/20) (b := 1/100) hD (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ
  have hscale := eventually_accurate_scale (a := (100:ℝ)^w/4) (by positivity) 0
  have hlarge := eventually_mul_le_double_exp (a := (100:ℝ)^w/8) (by positivity) (4*(100:ℝ)^w)
  have hm2 := (windowScale_tendsto 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [hmid,hbot,hscale,hlarge,eventually_window_tail_bounds hD ha ha1 W w hw,hm2]
    with m hmid hbot hscale hlarge htail hm2
  intro J hJ j hj
  simp only [pow_zero,one_mul] at hm2
  have hdata := hJ w hw j hj
  have hne := dyadic_dense_nonempty F hgood hδ hdata.2.2
  have hX2 : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hm2,hwp]
  have hm := dyadic_mean_bounds F hgood hX2 hne hdata.1 hdata.2.1
  have hpj := dyadic_prime_bounds F hgood j
  have hdense : δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(F.dyadicSieve hgood j).primes.card := by
    change δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(F.dyadicBatch j).card
    simpa only [pow_succ,mul_comm] using hdata.2.2
  have hT : Real.exp ((100:ℝ)^w*Real.exp m)≤(2:ℝ)^j := by
    rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hThi : Real.log ((2:ℝ)^j)≤(2*(100:ℝ)^w)*Real.exp m := by
    rw [Real.log_pow]
    nlinarith only [hdata.2.1,hX2]
  obtain ⟨_,hN,hlen,_,_⟩ := htail J (fun i hi k hk => (hJ i hi k hk).2.1)
  have hmid' := hmid (F.dyadicSieve hgood j) ((2:ℝ)^j) [] (windowBlocks a m J w) 0
    hne hpj hdense hT hThi
    (smaller_window_operations ha ha1 m w J (fun i hi k hk => (hJ i (hi.trans hw) k hk).2.1))
    (by simp only [Nat.cast_zero]; positivity) hlen
  have hTwo : (2:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) := by
    have he : 1≤Real.exp ((1/100)*Real.exp (m:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    linarith only [Real.add_one_le_exp (Real.exp ((1/100)*Real.exp (m:ℝ))),he]
  have hbot' := hbot (F.dyadicSieve hgood j) ((2:ℝ)^j) [] [] (windowSmoothing W m)
    hne hpj hdense
    ((Real.exp_le_exp.mpr (by nlinarith only [hwp,Real.exp_pos (m:ℝ)] : 1*Real.exp m≤(100:ℝ)^w*Real.exp m)).trans hT)
    hThi (by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]) hN
    (by simpa only [List.length_nil,Nat.cast_zero,zero_add] using hTwo)
  refine ⟨?_,?_,?_⟩
  · simpa only [List.nil_append,accurateBlock,middleBlocks] using hmid'
  · simpa only [List.nil_append,List.append_nil,accurateBlock] using hbot'
  · apply floor_size_lower (by linarith only [hX2]) (by linarith only [hm.1]) hm.2
    · simpa only [pow_zero,one_mul,div_div,show (4:ℝ)*2=8 by norm_num,div_mul_eq_mul_div] using hscale
    · simpa only [mul_assoc,div_mul_eq_mul_div] using hlarge


end QuadraticMoat
