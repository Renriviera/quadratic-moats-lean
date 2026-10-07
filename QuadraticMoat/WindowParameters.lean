import QuadraticMoat.AccurateScales
import QuadraticMoat.DyadicSieve
import OAI.NumberTheory.GaussianMoat.WindowParameters

/-! Native top-window entropy bands for supplied split-prime batches.
The original scalar schedule blocks and separated geometric sums are reused.
-/

universe uIota
namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
open Filter
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

theorem eventually_top_band {D a δ : ℝ} (hD : 1≤D) (ha : 0<a)
    (haδ : 2*a≤δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (s : SplitSieve Fld) (pre post : List ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes, Real.exp x≤(p:ℝ) ∧ (p:ℝ)≤2*Real.exp x) →
      δ*Real.exp x/Real.log (2*Real.exp x)≤ s.primes.card →
      (∀ n∈post, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp x)) →
      (post.length+2:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp x) →
      Nonempty (EntropyBand s D
        (pre++List.ofFn (fun i : Fin topIterations =>
          bandLength topParameter (a*Real.exp x) i.val)++post)
        0 (bandSize s topParameter (a*Real.exp x) topIterations) (1/10000)) ∧
      topCoefficient a*Real.exp x/(4*x)≤
        (bandSize s topParameter (a*Real.exp x) topIterations:ℝ) := by
  have hc := topCoefficient_pos ha
  have hlarge := eventually_poly_le_exp (2*bandConstant (Fld := Fld) D)
    (a := topParameter^5*topCoefficient a) (mul_pos (pow_pos topParameter_pos _) hc) 1
  filter_upwards [hlarge,eventually_ge_atTop (2:ℝ)] with x hlarge hx
  intro s pre post hne hp hdense hpost hlen
  have hT2 : 2≤Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hm := s.meanLog_bounds hne (Real.exp_pos x) hp
  rw [Real.log_exp] at hm
  have hmean : 1≤ s.meanLog := by linarith only [hm.1,hx]
  have hmean0 : 0< s.meanLog := by linarith only [hmean]
  have hlog2 : Real.log 2≤x := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh,hx]
  have hmean' : s.meanLog≤2*x := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hm
    linarith only [hm.2,hlog2]
  have hscale : bandScale topParameter (a*Real.exp x) topIterations=topCoefficient a*Real.exp x := by
    unfold bandScale topCoefficient; ring
  have hmargin : bandConstant (Fld := Fld) D*s.meanLog≤topParameter^5*
      bandScale topParameter (a*Real.exp x) topIterations := by
    have hh := mul_le_mul_of_nonneg_left hmean' (bandConstant_pos (Fld := Fld) D).le
    rw [hscale]
    simp only [pow_one] at hlarge
    nlinarith only [hh,hlarge]
  have hcap := dense_sieve_cap s hne hT2 hp hdense
    (by nlinarith only [haδ,Real.exp_pos x] : 2*(a*Real.exp x)≤δ*Real.exp x)
  have hband := entropyBand_from_margin s pre post 0 topIterations hD topParameter_pos
    topParameter_small (mul_pos ha (Real.exp_pos _)) hmean hmargin hcap
    (by simpa only [hscale,mul_assoc] using hpost)
    (by simp only [Nat.cast_zero]; positivity)
    (by simpa only [hscale,mul_assoc] using hlen) top_deficit
  refine ⟨hband,?_⟩
  have hg5 : topParameter^5≤1 := pow_le_one₀ topParameter_pos.le (by norm_num [topParameter])
  have hVpos := bandScale_pos topParameter_pos (mul_pos ha (Real.exp_pos x)) topIterations
  have hn := mul_le_mul_of_nonneg_right hg5 hVpos.le
  have hC : 2≤bandConstant (Fld := Fld) D := by
    unfold bandConstant
    linarith only [abs_nonneg (Real.log D),abs_nonneg (Real.log (ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ)))]
  have hm2 := mul_le_mul_of_nonneg_right hC hmean0.le
  have hV : 2*s.meanLog≤bandScale topParameter (a*Real.exp x) topIterations := by
    nlinarith only [hmargin,hn,hm2]
  have hh := bandSize_lower_of_scale hmean0
    (show 0<Real.log (Real.exp x) by rw [Real.log_exp]; linarith only [hx])
    (by simpa only [Real.log_exp] using hmean') hV (le_of_eq hscale.symm)
  simpa only [Real.log_exp] using hh

lemma residueWeight_union_le (F G : Finset (𝓞 Fld)) :
    residueWeight (F∪G)≤residueWeight F+residueWeight G := by
  classical
  have hh := Finset.sum_union_inter (s₁ := F) (s₂ := G) (f := fun f : (𝓞 Fld) => Real.log (integerAbsNorm Fld f))
  change residueWeight (F∪G)+residueWeight (F∩G)=residueWeight F+residueWeight G at hh
  linarith only [hh,residueWeight_nonneg (F∩G)]

lemma residueWeight_biUnion_le {ι : Type uIota} (J : Finset ι) (F : ι → Finset (𝓞 Fld)) :
    residueWeight (J.biUnion F)≤∑ j∈J, residueWeight (F j) := by
  induction J using Finset.induction_on with
  | empty => simp [residueWeight]
  | @insert j J hj ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hj]
    exact (residueWeight_union_le _ _).trans (add_le_add (le_refl _) ih)

variable (F : PrimeFamily) (hgood : ∀ p, F.good p → Nonempty (SplitPrime Fld p))

lemma separated_factor_cost (J : Finset ℕ) {K j : ℕ} (hK : 0<K)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcap : ∀ a∈J, a+K≤j) :
    residueWeight (J.biUnion (fun a => (F.dyadicSieve hgood a).selectedFactors))≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^j := by
  have hsum := Finset.sum_le_sum (fun a (_ : a∈J) => dyadicSieve_available_weight F hgood a)
  rw [←Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left (separated_power_sum J hK hsep hcap)
    (show 0≤4*Real.log 4 by positivity)
  have ht := (residueWeight_biUnion_le J (fun a => (F.dyadicSieve hgood a).selectedFactors)).trans (hsum.trans hh)
  calc
    _ ≤ 4*Real.log 4*((2:ℝ)^j/(2^K-1)) := ht
    _ = _ := by ring

theorem eventually_window_top {D a δ : ℝ} {K : ℕ}
    (hD : 1≤D) (ha : 0<a) (haδ : 2*a≤δ)
    (hgap : a≤(2:ℝ)^K*topCoefficient a) :
    ∀ᶠ X : ℝ in atTop, ∀ (J : Finset ℕ) (initial : List ℕ),
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) →
      (∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(F.dyadicBatch j).card) →
      ∀ j∈J, Nonempty (EntropyBand (F.dyadicSieve hgood j) D (initial++topBlocks a J)
        0 (bandSize (F.dyadicSieve hgood j) topParameter (a*(2:ℝ)^j) topIterations) (1/10000)) ∧
        topCoefficient a*(2:ℝ)^j/(4*Real.log ((2:ℝ)^j))≤
          (bandSize (F.dyadicSieve hgood j) topParameter (a*(2:ℝ)^j) topIterations:ℝ) := by
  have hδ : 0<δ := by linarith only [ha,haδ]
  have htop := eventually_top_band (Fld := Fld) hD ha haδ
  have hlen := eventually_poly_le_exp (100:ℝ)
    (a := topParameter*topCoefficient a) (mul_pos topParameter_pos (topCoefficient_pos ha)) 1
  obtain ⟨x0,h0⟩ := eventually_atTop.mp (htop.and hlen)
  filter_upwards [eventually_ge_atTop (max x0 2)] with X hX
  intro J initial hsep hJ j hj
  have hX2 : 2≤X := (le_max_right _ _).trans hX
  have hX0 : x0≤X := (le_max_left _ _).trans hX
  have hlog := (hJ j hj).1
  have hlog' := (hJ j hj).2.1
  obtain ⟨hband,hlen⟩ := h0 (j*Real.log 2) (hX0.trans hlog)
  have hn : (F.dyadicSieve hgood j).primes.Nonempty := by
    apply Finset.card_pos.mp
    have hlogp : 0<Real.log ((2:ℝ)^(j+1)) := by
      rw [Real.log_pow]
      positivity
    have hh := (hJ j hj).2.2
    have hp : 0<δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) := div_pos (by positivity) hlogp
    have hc : (0:ℝ)<(F.dyadicBatch j).card := hp.trans_le hh
    exact_mod_cast hc
  obtain ⟨pre,post,he,hpl,hpm⟩ := topBlocks_split (a := a) hj
  have hT : Real.exp (j*Real.log 2)=(2:ℝ)^j := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hcard := narrow_bins_card hX2 J (fun i hi => (hJ i hi).2.1)
  have hlen' : (post.length+2:ℝ)≤Real.exp (topParameter*topCoefficient a*(2:ℝ)^j) := by
    have hp : (post.length:ℝ)≤(J.card:ℝ)*topIterations := by exact_mod_cast hpl
    simp only [pow_one,hT] at hlen
    have he := Real.add_one_le_exp (topParameter*topCoefficient a*(2:ℝ)^j)
    norm_num only [topIterations,Nat.cast_ofNat] at hp
    nlinarith only [hp,hcard,hlen,he,hlog,hX2]
  have hprime : ∀ p∈(F.dyadicSieve hgood j).primes, Real.exp (j*Real.log 2)≤(p:ℝ) ∧
      (p:ℝ)≤2*Real.exp (j*Real.log 2) := by
    intro p hp
    rw [hT]
    have hh := (F.mem_dyadicBatch j p).mp hp
    constructor
    · exact_mod_cast hh.1
    · have hh' : p≤2^(j+1) := hh.2.1.le
      rw [pow_succ] at hh'
      exact_mod_cast (by simpa only [mul_comm] using hh' : p≤2*2^j)
  have hdense : δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (F.dyadicSieve hgood j).primes.card := by
    change δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (F.dyadicBatch j).card
    simpa only [hT,pow_succ,mul_comm] using (hJ j hj).2.2
  have hpst : ∀ n∈post, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp (j*Real.log 2)) := by
    intro n hnp
    obtain ⟨i,hi,hij,hni⟩ := hpm n hnp
    rw [hT]
    exact topBlock_separated ha hgap (hsep i hi j hj hij) n hni
  obtain ⟨hb,hbsize⟩ := hband (F.dyadicSieve hgood j) (initial++pre) post hn hprime hdense hpst
    (by simpa only [hT] using hlen')
  refine ⟨?_,?_⟩
  · simpa only [hT,he,topBlock,List.append_assoc] using hb
  · simpa only [hT,Real.log_pow] using hbsize


end QuadraticMoat
