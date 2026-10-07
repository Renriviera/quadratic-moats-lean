import QuadraticMoat.EntropyBand
import OAI.NumberTheory.GaussianMoat.AccurateScales

/-! Native entropy-band sizes and scalar certificate construction.

The field enters the geometric alphabet constant. The original accurate
scale, iteration, and elementary asymptotic lemmas are reused.
-/

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
open Filter
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

theorem entropyBand_from_suffix (s : SplitSieve Fld) (pre post : List ℕ) (N l : ℕ)
    {D g U δ : ℝ} (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hU : 0<U)
    (hL : 1≤ s.meanLog)
    (hlog : 2*(1+Real.log 18)≤g*bandScale g U l)
    (hlarge : 640*s.meanLog≤g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ))≤g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D≤bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hpost : ∀ n∈post, (n:ℝ)≤Real.exp (g*bandScale g U l))
    (hN : (N:ℝ)≤Real.exp (g*bandScale g U l))
    (hlen : (post.length+2:ℝ)≤Real.exp (g*bandScale g U l))
    (hconst : Real.log 36+2*Real.log D≤g*bandScale g U l)
    (hδ : (1/2:ℝ)^l+90*g≤δ) :
    Nonempty (EntropyBand s D
      (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post)
      N (bandSize s g U l) δ) := by
  let V := bandScale g U l
  have hV : 0<V := bandScale_pos hg hU l
  have hLp : 0<s.meanLog := by linarith only [hL]
  have hg5 : g^5≤1 := pow_le_one₀ hg.le (by linarith only [hg1])
  have hVL : 2*s.meanLog≤V := by
    have hh := mul_le_mul_of_nonneg_right hg5 hV.le
    change 640*s.meanLog≤g^5*V at hlarge
    nlinarith only [hlarge,hh,hLp]
  have hfloor : V/2≤(bandSize s g U l:ℝ)*s.meanLog := by
    have hh := Nat.lt_floor_add_one (V/s.meanLog)
    have hm := mul_lt_mul_of_pos_right hh hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    change V/2≤(⌊V/s.meanLog⌋₊:ℝ)*s.meanLog
    linarith only [hm,hVL]
  have hshift := commonSchedule_log_bound (fun _ => (0:𝓞 Fld)) post N hpost hN hlen
  simp only [commonSchedule_bound,Nat.cast_add] at hshift
  rw [show 1+((post.sum:ℝ)+N)=(post.sum:ℝ)+N+1 by ring] at hshift
  have hcost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1))≤
      (10*g)*(bandSize s g U l:ℝ)*s.meanLog := by
    rw [Real.log_mul (by linarith only [hD] : D≠0) (by positivity)]
    simp only [Nat.cast_add]
    have hc : Real.log 36+2*Real.log D≤g*V := hconst
    have hm := mul_le_mul_of_nonneg_left hfloor (show 0≤10*g by positivity)
    nlinarith only [hshift,hc,hm]
  exact ⟨⟨pre,post,g,U,l,10*g,rfl,rfl,hg,hg1,hU,hlog,hlarge,hsize,hdisp,hgeom,
    hcap,hcost,by linarith only [hδ]⟩⟩

noncomputable def bandConstant (D : ℝ) : ℝ :=
  10000+100*|Real.log D|+100*|Real.log (ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ))|

lemma bandConstant_pos (D : ℝ) : 0<bandConstant (Fld := Fld) D := by
  unfold bandConstant
  positivity

theorem entropyBand_from_margin (s : SplitSieve Fld) (pre post : List ℕ) (N l : ℕ)
    {D g U δ : ℝ} (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hU : 0<U)
    (hL : 1≤ s.meanLog)
    (hmargin : bandConstant (Fld := Fld) D*s.meanLog≤g^5*bandScale g U l)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hpost : ∀ n∈post, (n:ℝ)≤Real.exp (g*bandScale g U l))
    (hN : (N:ℝ)≤Real.exp (g*bandScale g U l))
    (hlen : (post.length+2:ℝ)≤Real.exp (g*bandScale g U l))
    (hδ : (1/2:ℝ)^l+90*g≤δ) :
    Nonempty (EntropyBand s D
      (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post)
      N (bandSize s g U l) δ) := by
  let V := bandScale g U l
  have hV : 0<V := bandScale_pos hg hU l
  have hg01 : g≤1 := by linarith only [hg1]
  have hg5 : g^5≤g := by
    have hh : g^4≤1 := pow_le_one₀ hg.le hg01
    calc g^5=g^4*g := by ring
         _ ≤ 1*g := mul_le_mul_of_nonneg_right hh hg.le
         _ = g := one_mul _
  have hg52 : g^5≤g^2 := by
    have hh : g^3≤1 := pow_le_one₀ hg.le hg01
    calc g^5=g^3*g^2 := by ring
         _ ≤ 1*g^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
         _ = g^2 := one_mul _
  have hC : bandConstant (Fld := Fld) D≤g^5*V := by
    have hh := mul_le_mul_of_nonneg_left hL (bandConstant_pos (Fld := Fld) D).le
    simp only [mul_one] at hh
    exact hh.trans hmargin
  have hCg := hC.trans (mul_le_mul_of_nonneg_right hg5 hV.le)
  have hCg2 := hC.trans (mul_le_mul_of_nonneg_right hg52 hV.le)
  have hCV := hCg.trans (by nlinarith only [hg01,hV] : g*V≤V)
  have hl16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<16)
  have hl18 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<18)
  have hl36 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<36)
  have hld := le_abs_self (Real.log D)
  have hla := le_abs_self (Real.log (ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ)))
  have ha := abs_nonneg (Real.log D)
  have hb := abs_nonneg (Real.log (ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ)))
  have hC640 : 640≤bandConstant (Fld := Fld) D := by unfold bandConstant; linarith only [ha,hb]
  apply entropyBand_from_suffix s pre post N l hD hg hg1 hU hL
  · dsimp only [bandConstant] at hCg
    linarith only [hCg,hl18,ha,hb]
  · exact (mul_le_mul_of_nonneg_right hC640 (by linarith only [hL])).trans hmargin
  · dsimp only [bandConstant] at hCg2
    linarith only [hCg2,hl16,hla,ha,hb]
  · dsimp only [bandConstant] at hCg
    nlinarith only [hCg,hl36,hld,ha,hb]
  · dsimp only [bandConstant] at hCV
    linarith only [hCV,hl16,hld,ha,hb]
  · exact hcap
  · exact hpost
  · exact hN
  · exact hlen
  · dsimp only [bandConstant] at hCg
    linarith only [hCg,hl36,hld,ha,hb]
  · exact hδ

lemma dense_sieve_cap (s : SplitSieve Fld) (hne : s.primes.Nonempty) {T δ U : ℝ}
    (hT : 2≤T)
    (hp : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hdense : δ*T/Real.log (2*T)≤ s.primes.card)
    (hsize : 2*U≤δ*T) : ⌊U/s.meanLog⌋₊≤ s.primes.card := by
  have hT0 : 0<T := by linarith only [hT]
  have hlogT : 0<Real.log T := Real.log_pos (by linarith only [hT])
  have hm := s.meanLog_bounds hne hT0 hp
  have hmean : 0<s.meanLog := hlogT.trans_le hm.1
  have hl2 : Real.log 2≤Real.log T := Real.log_le_log (by norm_num) hT
  have hhlog : Real.log (2*T)≤2*s.meanLog := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith only [hl2,hm.1]
  have hlo : 0<Real.log (2*T) := Real.log_pos (by linarith only [hT])
  have hd : δ*T≤(s.primes.card:ℝ)*Real.log (2*T) := (div_le_iff₀ hlo).mp hdense
  have hk : δ*T≤(s.primes.card:ℝ)*(2*s.meanLog) := hd.trans
    (mul_le_mul_of_nonneg_left hhlog (Nat.cast_nonneg _))
  apply Nat.floor_le_of_le
  apply (div_le_iff₀ hmean).mpr
  nlinarith only [hsize,hk]

theorem eventually_accurate_band {D A B a b δ : ℝ}
    (hD : 1≤D) (hA : 0<A) (ha : 0<a) (haA : a<A)
    (hba : b≤a/2) (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (s : SplitSieve Fld) (T : ℝ) (pre post : List ℕ) (N : ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) →
      δ*T/Real.log (2*T)≤ s.primes.card →
      Real.exp (A*Real.exp m)≤T → Real.log T≤B*Real.exp m →
      (∀ n∈post, (n:ℝ)≤Real.exp (Real.exp (b*Real.exp m))) →
      (N:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      (post.length+2:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      Nonempty (EntropyBand s D
        (pre++List.ofFn (fun i : Fin (accurateIterations m) =>
          bandLength (accurateGrid m) (Real.exp (a*Real.exp m)) i.val)++post)
        N (bandSize s (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m))
        (91*accurateGrid m)) := by
  have hlarge := eventually_mul_le_double_exp (a := a/2) (by positivity)
    (bandConstant (Fld := Fld) D*(B+1))
  have hgap := eventually_const_le_exp_mul (a := A-a) (by linarith only [haA]) (Real.log (2/δ))
  have htwo := eventually_const_le_exp_mul hA 2
  filter_upwards [eventually_accurate_scale ha 5,eventually_accurate_scale ha 1,
    eventually_accurate_small (show (0:ℝ)<1/200 by norm_num),hlarge,hgap,htwo]
    with m hm5 hm1 hsmall hlarge hgap htwo
  intro s T pre post N hne hp hdense hT hThi hpost hN hlen
  have he1 : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have hT0 : 0<T := (Real.exp_pos _).trans_le hT
  have hT2 : 2≤T := by
    have hh := Real.add_one_le_exp (A*Real.exp m)
    linarith only [hh,htwo,hT]
  have hm := s.meanLog_bounds hne hT0 hp
  have hmean : 1≤ s.meanLog := by
    have hh := Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at hh
    linarith only [hh,hm.1,htwo]
  have hl2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hmean' : s.meanLog≤(B+1)*Real.exp m := by
    rw [Real.log_mul (by norm_num) hT0.ne'] at hm
    nlinarith only [hm.2,hThi,hl2,he1]
  have hmargin := (mul_le_mul_of_nonneg_left hmean' (bandConstant_pos (Fld := Fld) D).le).trans
    (by simpa only [mul_assoc] using hlarge.trans hm5)
  have hsize : 2*Real.exp (a*Real.exp m)≤δ*T := by
    have he : Real.exp (a*Real.exp m+Real.log (2/δ))≤Real.exp (A*Real.exp m) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hgap]
    rw [Real.exp_add,Real.exp_log (div_pos (by norm_num) hδ)] at he
    have hh := mul_le_mul_of_nonneg_left (he.trans hT) hδ.le
    have heq : δ*(Real.exp (a*Real.exp m)*(2/δ))=2*Real.exp (a*Real.exp m) := by field_simp
    rwa [heq] at hh
  have hcap := dense_sieve_cap s hne hT2 hp hdense hsize
  have htail : Real.exp (b*Real.exp m)≤accurateGrid m*
      bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m) := by
    simpa only [pow_one, bandScale, OAI.GaussianMoat.bandScale] using ((Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hba (Real.exp_nonneg _))).trans hm1)
  exact entropyBand_from_margin s pre post N (accurateIterations m) hD (accurateGrid_pos m)
    hsmall (Real.exp_pos _) hmean hmargin hcap
    (fun n hn => (hpost n hn).trans (Real.exp_le_exp.mpr htail))
    (hN.trans (Real.exp_le_exp.mpr htail)) (hlen.trans (Real.exp_le_exp.mpr htail))
    (accurateIterations_error m)


lemma EntropyBand.size_cap {s : SplitSieve Fld} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) : b≤ s.primes.card := by
  rw [q.size]
  apply le_trans _ q.cap
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hmean.le
  have hh := bandScale_antitone q.positive.le (by linarith only [q.small]) q.scale.le (Nat.zero_le q.l)
  simpa only [bandScale,pow_zero,one_mul] using hh

lemma EntropyBand.size_lower {s : SplitSieve Fld} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) :
    bandScale q.g q.U q.l/2≤(b:ℝ)*s.meanLog := by
  have hV := bandScale_pos q.positive q.scale q.l
  have hg5 : q.g^5≤1 := pow_le_one₀ q.positive.le (by linarith only [q.small])
  have hh := mul_le_mul_of_nonneg_right hg5 hV.le
  have hlarge := q.large
  have hVL : 2*s.meanLog≤bandScale q.g q.U q.l := by nlinarith only [hh,hlarge,hmean]
  have hf := Nat.lt_floor_add_one (bandScale q.g q.U q.l/s.meanLog)
  have hm := mul_lt_mul_of_pos_right hf hmean
  rw [div_mul_cancel₀ _ hmean.ne',add_mul,one_mul] at hm
  have ht : bandScale q.g q.U q.l/2≤(⌊bandScale q.g q.U q.l/s.meanLog⌋₊:ℝ)*s.meanLog := by
    linarith only [hm,hVL]
  simpa only [q.size,bandSize] using ht

lemma EntropyBand.size_pos {s : SplitSieve Fld} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) : 0<b := by
  have hh := q.size_lower hmean
  have hV := bandScale_pos q.positive q.scale q.l
  by_contra h
  have hb : b=0 := by omega
  have he : (b:ℝ)=0 := by exact_mod_cast hb
  rw [he,zero_mul] at hh
  linarith only [hh,hV]

lemma bandSize_lower_of_scale {s : SplitSieve Fld} {g U C T : ℝ} {l : ℕ}
    (hmean : 0< s.meanLog) (hlog : 0<Real.log T)
    (hm : s.meanLog≤2*Real.log T)
    (hV : 2*s.meanLog≤bandScale g U l)
    (hscale : C*T≤bandScale g U l) :
    C*T/(4*Real.log T)≤(bandSize s g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/s.meanLog)
  have hh := mul_lt_mul_of_pos_right hf hmean
  rw [div_mul_cancel₀ _ hmean.ne',add_mul,one_mul] at hh
  have hlo : bandScale g U l/2≤(bandSize s g U l:ℝ)*s.meanLog := by
    change _≤(⌊bandScale g U l/s.meanLog⌋₊:ℝ)*_
    linarith only [hh,hV]
  have hu := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (bandSize s g U l))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hlo,hu,hscale]


end QuadraticMoat
