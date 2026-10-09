import QuadraticMoat.BatchParameters

namespace QuadraticMoat.BoundedFactors
open OAI.GaussianMoat

/-- The old repetition count already supports a logarithmic number of hits. -/
lemma soft_threshold_arithmetic {T p n L : ℝ} (hT : 0<T) (hp : 0<p)
    (hpT : p≤2*T) (hlog : 0≤Real.log (2*T))
    (hn : 256*T*Real.log (2*T)≤n*L) :
    Real.log (2*T)≤n*((L*((1/4)/p)/2))/8 := by
  have hh := mul_le_mul_of_nonneg_right hpT (show 0≤64*Real.log (2*T) by positivity)
  have hb : Real.log (2*T)≤n*L/(64*p) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hn,hh,mul_nonneg hT.le hlog]
  convert hb using 1 <;> ring

/-- Soft candidate lists allow empty lists and a logarithmic hit threshold. -/
lemma soft_package_list_arithmetic {X T p L n : ℝ} (hX : 1600≤X)
    (hT : Real.exp X≤T) (hpX : Real.exp X≤p) (hp : p≤2*T)
    (hn : 256*T*Real.log (2*T)≤n*L) :
    Real.log (1+4*(p*Real.exp (-X/200))+p*Real.exp
      (-n*((L*((1/4)/p)/2))/32))≤Real.log p-X/400 := by
  have hp0 : 0<p := (Real.exp_pos X).trans_le hpX
  have hT0 : 0<T := (Real.exp_pos X).trans_le hT
  have hlogT : X≤Real.log (2*T) := by
    have hh := Real.log_le_log (Real.exp_pos X) (hT.trans (show T≤2*T by linarith only [hT0]))
    simpa only [Real.log_exp] using hh
  have hl2 : Real.log (2:ℝ)≤1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hl4 : Real.log (4:ℝ)≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hl8 : Real.log (8:ℝ)≤3 := by
    rw [show (8:ℝ)=2^3 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hfirst : 4*Real.exp (-X/200)≤Real.exp (-X/400)/2 := by
    have hh := Real.exp_le_exp.mpr (show -X/200≤-X/400-Real.log 8 by linarith)
    rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<8)] at hh
    linarith only [hh]
  have hlarge : Real.log (2*T)/2≤n*L/(256*p) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hp (show 0≤128*Real.log (2*T) by linarith)
    nlinarith only [hn,hh]
  have htail : Real.exp (-n*((L*((1/4)/p)/2))/32)≤Real.exp (-X/400)/4 := by
    have heq : -n*((L*((1/4)/p)/2))/32 = -(n*L/(256*p)) := by ring
    rw [heq]
    have hh := Real.exp_le_exp.mpr
      (show -(n*L/(256*p))≤-X/400-Real.log 4 by linarith)
    rwa [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<4)] at hh
  have hone : 1≤p*Real.exp (-X/400)/4 := by
    have he : (4:ℝ)≤Real.exp (X-X/400) := by
      have hh := Real.add_one_le_exp (X-X/400)
      linarith only [hh,hX]
    have hh := mul_le_mul_of_nonneg_right hpX (Real.exp_nonneg (-X/400))
    rw [←Real.exp_add, show X + -X/400 = X-X/400 by ring] at hh
    linarith only [hh,he]
  have harg : 1+4*(p*Real.exp (-X/200))+p*Real.exp
      (-n*((L*((1/4)/p)/2))/32)≤p*Real.exp (-X/400) := by
    have h1 := mul_le_mul_of_nonneg_left hfirst hp0.le
    have h2 := mul_le_mul_of_nonneg_left htail hp0.le
    nlinarith only [h1,h2,hone]
  have hh := Real.log_le_log (by positivity) harg
  rw [Real.log_mul hp0.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  linarith only [hh]

/-- A constant entropy bit per selected coordinate is absorbed at large scales. -/
lemma soft_package_rate_arithmetic {X T L n b H E c mean loss : ℝ}
    (hX : 10000≤X) (hT : 0<T) (hc : 0<c)
    (hlog : X≤Real.log T) (hlog' : Real.log T≤21/20*X)
    (hmean : mean≤2*X) (hb : c*T/Real.log T≤b)
    (hn : n*L≤1024*T*Real.log T)
    (hshift : 2*n*H≤c*T/5000) (hE : E≤c*T/10000)
    (hloss : n*L*loss≤c*T/10000) :
    n*(L*(c/(10000000*Real.log T)+loss)+2*H)≤
      b*((X/400)*(1-2*(1/100))-(1/10000)*mean-Real.log 2)-E := by
  have hlog0 : 0<Real.log T := by linarith only [hX,hlog]
  have hb0 : 0<b := (div_pos (mul_pos hc hT) hlog0).trans_le hb
  have hbg : c*T≤b*Real.log T := (div_le_iff₀ hlog0).mp hb
  have hbg' : c*T≤b*(21/20*X) := hbg.trans (mul_le_mul_of_nonneg_left hlog' hb0.le)
  have hl2 : Real.log (2:ℝ)≤1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hgain : X/500≤(X/400)*(1-2*(1/100))-(1/10000)*mean-Real.log 2 := by
    nlinarith only [hmean,hX,hl2]
  have hrev := mul_le_mul_of_nonneg_left hgain hb0.le
  have hcost := mul_le_mul_of_nonneg_right hn (show 0≤c/(10000000*Real.log T) by positivity)
  have heq : (1024*T*Real.log T)*(c/(10000000*Real.log T))=1024*c*T/10000000 := by
    field_simp
  rw [heq] at hcost
  nlinarith only [hbg',hrev,hcost,hshift,hE,hloss,mul_pos hc hT]

open Filter

/-- The existing terminal smoothing overwhelms the extra true-hit shift cost. -/
lemma eventually_soft_smoothing_loss {c : ℝ} (hc : 0<c) :
    ∀ᶠ X : ℝ in atTop, ∀ n L b N T : ℝ,
      0≤n → 0≤L → 0≤b → 0≤N → Real.exp X≤T →
      n≤Real.exp (7/10*X) → L≤Real.exp (21/50*X) →
      b≤2*Real.exp (21/20*X) → Real.exp (20*X)≤N →
      n*L*(b*L/(N+1))≤c*T/10000 := by
  have hsmall := eventually_mul_exp_le_exp (a := 159/100) (b := 20)
    (by norm_num) (20000/c)
  filter_upwards [hsmall] with X hsmall
  intro n L b N T hn0 hL0 hb0 hN0 hT hn hL hb hN
  have hprod : n*L*(b*L)≤2*Real.exp (259/100*X) := by
    calc
      n*L*(b*L) ≤ Real.exp (7/10*X)*Real.exp (21/50*X)*
          ((2*Real.exp (21/20*X))*Real.exp (21/50*X)) := by gcongr
      _ = 2*Real.exp (259/100*X) := by
        rw [show Real.exp (7/10*X)*Real.exp (21/50*X)*
          ((2*Real.exp (21/20*X))*Real.exp (21/50*X)) =
          2*(Real.exp (7/10*X)*Real.exp (21/50*X)*Real.exp (21/20*X)*Real.exp (21/50*X)) by ring]
        simp only [←Real.exp_add]
        congr 2
        ring
  have hsmall' := mul_le_mul_of_nonneg_left hsmall hc.le
  have heq : c*(20000/c*Real.exp (159/100*X))=20000*Real.exp (159/100*X) := by field_simp
  rw [heq] at hsmall'
  have hlarge := mul_le_mul_of_nonneg_right hsmall' (Real.exp_nonneg X)
  have heq' : (20000*Real.exp (159/100*X))*Real.exp X = 20000*Real.exp (259/100*X) := by
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  rw [heq'] at hlarge
  have hT0 : 0≤T := (Real.exp_pos X).le.trans hT
  have hupper : (c*Real.exp (20*X))*Real.exp X≤c*T*(N+1) := by
    calc
      _ = c*Real.exp X*Real.exp (20*X) := by ring
      _ ≤ c*T*(N+1) := by gcongr <;> linarith
  have hfinal := hlarge.trans hupper
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by linarith : 0<N+1)).mpr
  nlinarith only [hprod,hfinal]

end QuadraticMoat.BoundedFactors
