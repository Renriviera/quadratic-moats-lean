import QuadraticMoat.BoundedFactors.SoftWalkPackage
import QuadraticMoat.InformationTelescope

namespace QuadraticMoat.BoundedFactors
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
universe uOmega uKappa
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

theorem soft_exists_batch_information {Ω : Type uOmega} {κ : Type uKappa} [Fintype Ω]
    (s : SplitSieve Fld) (hne : s.primes.Nonempty) (p : FinLaw Ω) (a : Ω → ℕ)
    (g : κ → (𝓞 Fld)) (R : ForwardKernel) (z : ℕ → (𝓞 Fld))
    (hz : Function.Injective z)
    {b L N n : ℕ} (hb : b≤ s.primes.card) (hn : 0<n) (hL : 0<L)
    {D τ A η δ E r h U C : ℝ} (hD : 1≤D) (hτ : 0<τ) (hA : 0≤A) (hh : 0<h)
    (hU : 0≤U) (hC : 0≤C) (hcharge : U/h≤C)
    (hlog : ∀ i, Real.log (s.signedPrime i)≤U)
    (hcut : ∀ i, h≤(n:ℝ)*((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/8)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : s.SignedIndex → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy p (fun ω => z (a ω)) b)
    (hO : p.Hf (fun ω i => residueCode (g i) (z (a ω)))≤E)
    (hBad : (𝔼 i : s.SignedIndex, p.prob (fun ω => e i≤
      ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z (a ω) i).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (1+4*e i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/32))) ≤
        Real.log (s.signedPrime i)-A)
    (hrate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(R.bound+N)))+
      (L:ℝ)*C*((b:ℝ)*(L:ℝ)/(N+1))) ≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E-(b:ℝ)*Real.log 2) :
    ∃ σ : Fin s.primes.card → Bool, ∃ π : Equiv.Perm (Fin s.primes.card),
      r≤ (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω))).cIf
        (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j))
          (z (a v.1+v.2.val)))
        (fun v => incrementWord z L (a v.1+v.2.val))
        (fun v i => residueCode (g i) (z (a v.1+v.2.val))) / L +
        C*lawHitMass (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω)))
          (fun v => z (a v.1+v.2.val)) s.selectedFactors := by
  let K := R.then (smoothingKernel N)
  let old := fun ω i => residueCode (g i) (z (a ω))
  let old' := FinLaw.outputCode old
  have hOld : p.Hf old'≤E := by
    apply le_trans (le_of_eq (p.Hf_eq_of_fibers old' old (fun ω ν => FinLaw.outputCode_eq_iff old ω ν))) hO
  have hD0 : 0≤D := by linarith only [hD]
  have hlower := soft_averaged_batch_package_information s hne p a old' R z hz hb
    hD0 hτ hA hh hL hU hlog hcut hs e he hshort hLN herr hH hOld hBad hnum
  let Info := fun (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) =>
    (p.joint (fun ω => K.law (a ω))).cIf
      (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z (a v.1+v.2.val)))
      (fun v => incrementWord z L (a v.1+v.2.val))
      (fun v i => residueCode (g i) (z (a v.1+v.2.val)))
  have hK : 1≤K.bound := by change 1≤R.bound+N; omega
  have ht (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      (p.joint (fun ω => ForwardKernel.packageLaw K z hD0 hs (a ω) L)).cIf
        (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1))) Prod.snd
        (fun v => old' v.1) ≤ Info σ π+2*(Real.log 36+2*Real.log (D*K.bound)) := by
    have hc := (p.joint (fun ω => ForwardKernel.packageLaw K z hD0 hs (a ω) L)).cIf_congr_fibers
      (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1)))
      (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z (a v.1)))
      Prod.snd Prod.snd (fun v => old' v.1) (fun v => old v.1)
      (fun v w => by
        simp only [funext_iff,SplitSieve.residue,ringResidue_eq,residueCode_eq])
      (fun _ _ => Iff.rfl) (fun v w => FinLaw.outputCode_eq_iff old v.1 w.1)
    rw [hc]
    exact ForwardKernel.package_information_transport K p a (fun j => s.signedFactorAt (s.selectedIndex hb σ π j))
      g z hD hs hK L
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => ht σ π))
  simp only [Finset.expect_add_distrib,Fintype.expect_const] at hav
  have hmul := mul_le_mul_of_nonneg_left hav (Nat.cast_nonneg n)
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  let M := lawHitMass (p.joint (fun ω => K.law (a ω)))
    (fun v => z (a v.1+v.2.val)) s.selectedFactors
  have hM : 0≤M := lawHitMass_nonneg _ _ _
  have hmass : ((n:ℝ)/h)*U*(L:ℝ)*(M+(b:ℝ)*(L:ℝ)/(N+1)) ≤
      (n:ℝ)*(L:ℝ)*C*(M+(b:ℝ)*(L:ℝ)/(N+1)) := by
    have ht := mul_le_mul_of_nonneg_left hcharge
      (show 0≤(n:ℝ)*(L:ℝ)*(M+(b:ℝ)*(L:ℝ)/(N+1)) by positivity)
    convert ht using 1 <;> ring
  have hrate' : (L:ℝ)*(r-C*M)≤𝔼 σ, 𝔼 π, Info σ π := by
    have heK : (K.bound:ℝ)=R.bound+N := by simp only [K,ForwardKernel.then,smoothingKernel,Nat.cast_add]
    conv at hmul => rhs; rw [heK]
    change _-((n:ℝ)/h)*U*(L:ℝ)*(M+(b:ℝ)*(L:ℝ)/(N+1))≤_ at hlower
    have hlow := hlower.trans hmul
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith only [hlow, hrate, hmass]
  obtain ⟨σ,_,hσ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hrate'
  obtain ⟨π,_,hπ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hσ
  refine ⟨σ,π,?_⟩
  have hselected : r-C*M≤Info σ π/(L:ℝ) :=
    (le_div_iff₀ (show (0:ℝ)<L by exact_mod_cast hL)).mpr
      (by nlinarith only [hπ])
  change r≤Info σ π/(L:ℝ)+C*M
  linarith only [hselected]

theorem soft_schedule_batch_information (s : SplitSieve Fld) (hne : s.primes.Nonempty)
    (z : ℕ → (𝓞 Fld)) (hz : Function.Injective z)
    (pre rest : List ℕ) {N b L n : ℕ} {D T τ A η δ E r h U C : ℝ}
    (hD : 1≤D) (hDscale : ctx.scale≤D) (hT : 5≤T) (hML : 1≤ s.meanLog)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (band : EntropyBand s D pre 0 b δ)
    (u : s.SignedIndex → ℝ) (coverage : CoverageDerivation s D N rest τ u η)
    {κ : Type uKappa} (f : κ → (𝓞 Fld))
    (hOld : ((TimeLaw.at 0).advance (commonSchedule z pre 0)).law.Hf
      (fun t i => residueCode (f i) (z t.val))≤E)
    (hb : b≤ s.primes.card) (hn : 0<n) (hL : 0<L) (hτ : 0<τ) (hA : 0≤A)
    (hh : 0<h) (hU : 0≤U) (hC : 0≤C) (hcharge : U/h≤C)
    (hlog : ∀ i, Real.log (s.signedPrime i)≤U)
    (hcut : ∀ i, h≤(n:ℝ)*((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/8)
    (hu : ∀ i, 0≤u i) (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hnum : ∀ i, Real.log (1+4*u i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/32)))≤Real.log (s.signedPrime i)-A)
    (hrate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(rest.sum+N)))+
      (L:ℝ)*C*((b:ℝ)*(L:ℝ)/(N+1)))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E-(b:ℝ)*Real.log 2) :
    ∃ σ : Fin s.primes.card → Bool, ∃ π : Equiv.Perm (Fin s.primes.card),
      r≤TimeLaw.info ((TimeLaw.at 0).advance (commonSchedule z (pre++rest) N))
        (fun a j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z a))
        (incrementWord z L) (fun a i => residueCode (f i) (z a)) / L+
      C*hitMass ((TimeLaw.at 0).advance (commonSchedule z (pre++rest) N)) z s.selectedFactors := by
  let P := (TimeLaw.at 0).advance (commonSchedule z pre 0)
  let R := commonSchedule z rest 0
  have hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy P.law (fun t => z t.val) b := by
    rw [SplitSieve.pointEntropy_exact_start]
    simpa only [Nat.zero_add] using band.sound hne z hz hD hDscale hT hs hpT hML 0
  have hc := coverage.sound hne z hz hD hDscale hT hs hpT hML
  have hBad : (𝔼 i : s.SignedIndex, P.law.prob (fun ω => u i≤
      ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z ω.val i).lowResidues τ).card))≤η := by
    let := s.signedIndex_nonempty hne
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
      mul_le_mul_of_nonneg_left (hc ω.val) (P.law.nonneg ω))
    simp only [← Finset.sum_mul,P.law.sum_one,one_mul] at hh
    rw [← commonSchedule_smooth]
    unfold FinLaw.prob at hh ⊢
    rw [Finset.expect_eq_sum_div_card]
    simp only [FinLaw.uniform,Finset.mul_sum,mul_ite,mul_zero] at hh
    rw [Finset.sum_comm] at hh
    convert hh using 1
    all_goals first | rfl | simp only [Finset.card_univ,div_eq_mul_inv,Finset.sum_mul,ite_mul,zero_mul]
  obtain ⟨σ,π,hh⟩ := soft_exists_batch_information s hne P.law (fun t => t.val) f R z hz
    hb hn hL hD hτ hA hh hU hC hcharge hlog hcut hs u hu hshort hLN herr hH hOld hBad hnum
    (by simpa only [R,commonSchedule_bound,Nat.add_zero] using hrate)
  refine ⟨σ,π,?_⟩
  have heR : commonSchedule z rest N=R.then (smoothingKernel N) := commonSchedule_smooth z rest N
  rw [commonSchedule_append,TimeLaw.advance_then,TimeLaw.advance_info,advance_hitMass,heR]
  exact hh



end QuadraticMoat.BoundedFactors
