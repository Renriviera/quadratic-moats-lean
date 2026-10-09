import QuadraticMoat.BoundedFactors.HitBudget
import QuadraticMoat.BoundedFactors.SoftInformation

namespace QuadraticMoat.BoundedFactors
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
universe uOmega uOutput uIota
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

lemma package_true_hit_iff (R : ForwardKernel) (f : 𝓞 Fld) (z : ℕ → 𝓞 Fld)
    {D : ℝ} (hD : 0 ≤ D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (a L : ℕ) (u : Fin (R.bound+1)) :
    WalkPackage.Hits f (ForwardKernel.packageSymbol R z hD hs a L u)
      (ringResidue f (z a)) ↔ ∃ l : Fin L, f ∣ z (a+u.val+l.val) := by
  simp only [WalkPackage.Hits, ForwardKernel.packageSymbol_prefix]
  apply exists_congr
  intro l
  rw [ringResidue_sub, sub_eq_neg_self, ← ringResidue_zero, ringResidue_eq, sub_zero]

lemma smoothed_prob_shift_le (R : ForwardKernel) (N a l : ℕ) (hl : l ≤ N)
    (E : ℕ → Prop) :
    ((R.then (smoothingKernel N)).law a).prob (fun u => E (a+u.val+l)) ≤
    ((R.then (smoothingKernel N)).law a).prob (fun u => E (a+u.val)) +
      (l:ℝ)/(N+1) := by
  let Q := (R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))
  have hh := (R.law a).smoothing_prob (fun u => a+u.val) N l hl (fun t => ¬E t)
  rw [FinLaw.prob_compl, FinLaw.prob_compl] at hh
  have he : ∀ k, ((R.then (smoothingKernel N)).law a).prob (fun u => E (a+u.val+k)) =
      Q.prob (fun v => E (a+v.1.val+v.2.val+k)) := by
    intro k
    change (Q.map (addOffsets R.bound N)).prob (fun (u : Fin (R.bound+N+1)) => E (a+u.val+k)) = _
    rw [FinLaw.prob_map]
    simp only [addOffsets, Nat.add_assoc]
  rw [he l]
  have he0 := he 0
  simp only [Nat.add_zero] at he0
  rw [he0]
  linarith only [hh]

lemma smoothed_package_true_hit_le (R : ForwardKernel) (f : 𝓞 Fld)
    (z : ℕ → 𝓞 Fld) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (a L N : ℕ) (hLN : L ≤ N) :
    (ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs a L).prob
      (fun v => WalkPackage.Hits f v (ringResidue f (z a))) ≤
    (L:ℝ) * (((R.then (smoothingKernel N)).law a).prob
      (fun u => f ∣ z (a+u.val)) + (L:ℝ)/(N+1)) := by
  rw [ForwardKernel.packageLaw, FinLaw.prob_map]
  simp only [package_true_hit_iff]
  apply le_trans (FinLaw.prob_exists_le_sum ((R.then (smoothingKernel N)).law a)
    (fun (l : Fin L) u => f ∣ z (a+u.val+l.val)))
  have hh (l : Fin L) :
      ((R.then (smoothingKernel N)).law a).prob (fun u => f ∣ z (a+u.val+l.val)) ≤
      ((R.then (smoothingKernel N)).law a).prob (fun u => f ∣ z (a+u.val)) + (L:ℝ)/(N+1) := by
    apply (smoothed_prob_shift_le R N a l.val (by omega) (fun t => f ∣ z t)).trans
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (by exact_mod_cast l.isLt.le) (by positivity)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun l _ => hh l)

lemma joint_smoothed_package_true_hit_le {Ω : Type uOmega} [Fintype Ω]
    (p : FinLaw Ω) (a : Ω → ℕ) (R : ForwardKernel) (f : 𝓞 Fld)
    (z : ℕ → 𝓞 Fld) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (L N : ℕ) (hLN : L ≤ N) :
    (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).prob
      (fun v => WalkPackage.Hits f v.2 (ringResidue f (z (a v.1)))) ≤
    (L:ℝ)*((p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω))).prob
      (fun v => f ∣ z (a v.1+v.2.val)) + (L:ℝ)/(N+1)) := by
  rw [FinLaw.prob_joint, FinLaw.prob_joint]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (smoothed_package_true_hit_le R f z hD hs (a ω) L N hLN)
      (p.nonneg ω))
  convert hh using 1
  symm
  calc
    _ = ∑ ω, ((L:ℝ)*(p ω*((R.then (smoothingKernel N)).law (a ω)).prob
        (fun u => f ∣ z (a ω+u.val)))+p ω*((L:ℝ)*((L:ℝ)/(N+1)))) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, p.sum_one]
      ring

theorem soft_smoothed_batch_package_information {Ω : Type uOmega} {O : Type uOutput} {ι : Type uIota}
    [Fintype Ω] [Fintype O] [Fintype ι]
    (s : SplitSieve Fld) (p : FinLaw Ω) (a : Ω → ℕ) (old : Ω → O)
    (I : ι → s.SignedIndex) (R : ForwardKernel)
    (z : ℕ → (𝓞 Fld)) (hz : Function.Injective z)
    {D τ A H η h : ℝ} {L N n : ℕ}
    (hD : 0≤D) (hτ : 0<τ) (hA : 0≤A) (hh : 0<h) (hL : 0<L)
    (hcut : ∀ i, h≤(n:ℝ)*((L:ℝ)*(τ/(s.signedPrime (I i):ℝ))/2)/8)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : ι → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime (I i):ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime (I i):ℝ))/2)
    (hH : (∑ i, Real.log (s.signedPrime (I i)))-H ≤
      p.cHf (fun ω i => s.residue (I i) (z (a ω))) old)
    (hBad : (∑ i, p.prob (fun ω => e i≤
      ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z (a ω) (I i)).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (1+4*e i+(s.signedPrime (I i):ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime (I i):ℝ))/2)/32))) ≤
        Real.log (s.signedPrime (I i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H-(Fintype.card ι:ℝ)*Real.log 2-
      ((n:ℝ)/h)*(∑ i, Real.log (s.signedPrime (I i))*
        (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).prob
          (fun v => WalkPackage.Hits (s.signedFactorAt (I i)) v.2 (s.residue (I i) (z (a v.1))))) ≤ (n:ℝ)*
      (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).cIf
        (fun v i => s.residue (I i) (z (a v.1))) Prod.snd (fun v => old v.1) := by
  let K := R.then (smoothingKernel N)
  let q := fun ω => ForwardKernel.packageLaw K z hD hs (a ω) L
  let Good := fun i ω =>
    (((ForwardKernel.relativeResidueLaw K s z (a ω) (I i)).lowResidues τ).card:ℝ)<e i
  have hb := FinLaw.posterior_soft_information_lower (fun i => s.Residue (I i)) p old
    (fun ω i => s.residue (I i) (z (a ω))) q (fun i => WalkPackage.Hits (s.signedFactorAt (I i)))
    Good (fun i ω => ForwardKernel.passingException K s z (a ω) (I i) τ) e
    (fun i => (L:ℝ)*(τ/(s.signedPrime (I i):ℝ))/2) n hA hh he
    (fun i => by
      have hp := (s.prime_mem _ (s.enumeration (I i).2).property).pos
      positivity) hcut
    (by
      intro i ω hg
      rw [ForwardKernel.passingException_card]
      exact hg.le)
    (by
      intro i ω _ x hx
      apply ForwardKernel.smoothed_package_floor R (s.signedFactorAt (I i)) z hz hD hs
        (by simpa only [s.signedFactorAt_norm] using hshort i) hLN (herr i) (a ω) x
      have hxhit := ForwardKernel.not_mem_passingException K s z (a ω) (I i) τ x hx
      simpa only [ForwardKernel.relativeResidueLaw,FinLaw.mass_map_eq_prob,SplitSieve.residue] using hxhit)
    (by simpa only [s.residue_card] using hH)
    (by simpa only [Good,not_lt] using hBad)
    (by simpa only [s.residue_card, mul_div_assoc] using hnum)
  simpa only [s.residue_card] using hb



lemma selected_factor_injective (s : SplitSieve Fld) {b : ℕ} (hb : b≤ s.primes.card)
    (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
    Function.Injective (fun j => s.signedFactorAt (s.selectedIndex hb σ π j)) := by
  intro j k hjk
  have he := congrArg (integerAbsNorm Fld) hjk
  simp only [s.signedFactorAt_norm, SplitSieve.signedPrime, SplitSieve.selectedIndex] at he
  have hen := s.enumeration.injective (Subtype.ext he)
  have hep := π.injective hen
  have hv : j.val=k.val := congrArg (fun x : Fin s.primes.card => x.val) hep
  exact Fin.ext hv

lemma selected_true_hit_weight_le {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve Fld) (p : FinLaw Ω) (a : Ω → ℕ) (R : ForwardKernel)
    (z : ℕ → 𝓞 Fld) {D U : ℝ} (hD : 0≤D) (hU : 0≤U)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    {L N b : ℕ} (hLN : L≤N) (hb : b≤ s.primes.card)
    (hlog : ∀ i, Real.log (s.signedPrime i)≤U)
    (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
    (∑ j : Fin b, Real.log (s.signedPrime (s.selectedIndex hb σ π j))*
      (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).prob
        (fun v => WalkPackage.Hits (s.signedFactorAt (s.selectedIndex hb σ π j)) v.2
          (s.residue (s.selectedIndex hb σ π j) (z (a v.1))))) ≤
    U*(L:ℝ)*(lawHitMass (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω)))
      (fun v => z (a v.1+v.2.val)) s.selectedFactors + (b:ℝ)*(L:ℝ)/(N+1)) := by
  let Q := p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω))
  let Z := fun v : Ω × Fin ((R.then (smoothingKernel N)).bound+1) => z (a v.1+v.2.val)
  have hh (j : Fin b) :
      Real.log (s.signedPrime (s.selectedIndex hb σ π j))*
      (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).prob
        (fun v => WalkPackage.Hits (s.signedFactorAt (s.selectedIndex hb σ π j)) v.2
          (s.residue (s.selectedIndex hb σ π j) (z (a v.1)))) ≤
      U*(L:ℝ)*(Q.prob (fun v => s.signedFactorAt (s.selectedIndex hb σ π j)∣Z v)+(L:ℝ)/(N+1)) := by
    have ht := joint_smoothed_package_true_hit_le p a R
      (s.signedFactorAt (s.selectedIndex hb σ π j)) z hD hs L N hLN
    have hl := mul_le_mul_of_nonneg_right (hlog (s.selectedIndex hb σ π j))
      ((p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L )).prob_nonneg
        (fun v => WalkPackage.Hits (s.signedFactorAt (s.selectedIndex hb σ π j)) v.2
          (s.residue (s.selectedIndex hb σ π j) (z (a v.1)))))
    exact hl.trans (by simpa only [mul_assoc, Q, Z, SplitSieve.residue] using mul_le_mul_of_nonneg_left ht hU)
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh j)
  have hbmass := selected_sum_le_lawHitMass Q Z s.selectedFactors
    (fun j : Fin b => s.signedFactorAt (s.selectedIndex hb σ π j))
    (selected_factor_injective s hb σ π) (fun j => s.signed_mem_selectedFactors _)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht
  apply ht.trans
  simpa only [Q,Z,mul_div_assoc] using
    mul_le_mul_of_nonneg_left (add_le_add hbmass (le_refl ((b:ℝ)*((L:ℝ)/(N+1)))))
      (show 0≤U*(L:ℝ) by positivity)

theorem soft_averaged_batch_package_information {Ω : Type uOmega} {O : Type uOutput} [Fintype Ω] [Fintype O]
    (s : SplitSieve Fld) (hne : s.primes.Nonempty) (p : FinLaw Ω) (a : Ω → ℕ)
    (old : Ω → O) (R : ForwardKernel) (z : ℕ → (𝓞 Fld))
    (hz : Function.Injective z)
    {b L N n : ℕ} (hb : b≤ s.primes.card) {D τ A η δ E h U : ℝ}
    (hD : 0≤D) (hτ : 0<τ) (hA : 0≤A) (hh : 0<h) (hL : 0<L)
    (hU : 0≤U) (hlog : ∀ i, Real.log (s.signedPrime i)≤U)
    (hcut : ∀ i, h≤(n:ℝ)*((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/8)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : s.SignedIndex → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy p (fun ω => z (a ω)) b)
    (hO : p.Hf old≤E)
    (hBad : (𝔼 i : s.SignedIndex, p.prob (fun ω => e i≤
      ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z (a ω) i).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (1+4*e i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/32))) ≤
        Real.log (s.signedPrime i)-A) :
    (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E-(b:ℝ)*Real.log 2-
      ((n:ℝ)/h)*U*(L:ℝ)*(lawHitMass (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω)))
        (fun v => z (a v.1+v.2.val)) s.selectedFactors+(b:ℝ)*(L:ℝ)/(N+1)) ≤ (n:ℝ)*
      (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
        (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).cIf
          (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1)))
          Prod.snd (fun v => old v.1)) := by
  let X := fun (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card))
    (ω : Ω) (j : Fin b) => s.residue (s.selectedIndex hb σ π j) (z (a ω))
  let Bad := fun i => p.prob (fun ω => e i≤
    ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z (a ω) i).lowResidues τ).card)
  have hi0 (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :=
    soft_smoothed_batch_package_information s p a old (s.selectedIndex hb σ π) R z hz
      hD hτ hA hh hL (fun j => hcut _) hs (fun j => e (s.selectedIndex hb σ π j))
      (fun j => he _) (fun j => hshort _) hLN (fun j => herr _)
      (H := (∑ j, Real.log (s.signedPrime (s.selectedIndex hb σ π j)))-p.cHf (X σ π) old)
      (by dsimp only [X]; linarith)
      (η := ∑ j, Bad (s.selectedIndex hb σ π j)) le_rfl (fun j => hnum _)
  let loss := ((n:ℝ)/h)*U*(L:ℝ)*(lawHitMass (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω)))
    (fun v => z (a v.1+v.2.val)) s.selectedFactors+(b:ℝ)*(L:ℝ)/(N+1))
  have hi (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      A*((b:ℝ)-2*(∑ j : Fin b, Bad (s.selectedIndex hb σ π j)))-
      ((∑ j : Fin b, Real.log (s.signedPrime (s.selectedIndex hb σ π j)))-p.cHf (X σ π) old)-
      (b:ℝ)*Real.log 2-loss ≤ (n:ℝ)*
      (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).cIf
        (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1))) Prod.snd (fun v => old v.1) := by
    have hw := selected_true_hit_weight_le s p a R z hD hU hs hLN hb hlog σ π
    have hm := mul_le_mul_of_nonneg_left hw (div_nonneg (Nat.cast_nonneg n) hh.le)
    have ht := hi0 σ π
    simp only [Fintype.card_fin] at ht
    dsimp only [loss]
    nlinarith only [hm,ht]
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hi σ π))
  simp only [Fintype.card_fin,Finset.expect_sub_distrib,← Finset.mul_expect,Fintype.expect_const,
    Finset.expect_sum_comm] at hav
  have hx (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      p.Hf (X σ π)-E≤p.cHf (X σ π) old := by
    have h := p.Hf_pair_ge_snd old (X σ π)
    rw [p.Hf_pair_comm] at h
    unfold FinLaw.cHf
    linarith only [h,hO]
  have hxa := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hx σ π))
  simp only [Finset.expect_sub_distrib,Fintype.expect_const] at hxa
  have hxe := s.selected_entropy_average p (fun ω => z (a ω)) hb
  change (𝔼 σ, 𝔼 π, p.Hf (X σ π))=_ at hxe
  rw [hxe] at hxa
  have hlog := s.selected_log_average hne hb
  have hbad := s.selected_sum_average hne hb Bad
  have hbR : 0≤(b:ℝ) := Nat.cast_nonneg _
  have hbadle : (b:ℝ)*(𝔼 i, Bad i)≤b*η := mul_le_mul_of_nonneg_left hBad hbR
  simp only [Finset.expect_sum_comm] at hlog hbad
  rw [hlog,hbad] at hav
  have hprod := mul_le_mul_of_nonneg_left hbadle hA
  change _-loss≤_
  nlinarith only [hav,hxa,hH,hprod]



end QuadraticMoat.BoundedFactors
