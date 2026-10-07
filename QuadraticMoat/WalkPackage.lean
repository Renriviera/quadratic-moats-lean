import QuadraticMoat.PassingInformation
import QuadraticMoat.WalkWords
import QuadraticMoat.Information
import OAI.NumberTheory.GaussianMoat.WalkPackage

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
universe uOmega uAlpha uOutput uIota uKappa
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

abbrev WalkPackage (D : ℝ) (B L : ℕ) := planeBall (K := Fld) (D*B) × (Fin L → planeBall (K := Fld) D)

noncomputable def ForwardKernel.packageSymbol (K : ForwardKernel)
    (z : ℕ → (𝓞 Fld)) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) (u : Fin (K.bound+1)) :
    WalkPackage (Fld := Fld) D K.bound L :=
  (ForwardKernel.displacementSymbol K z hD hs a u,boundedWord z hs L (a+u.val))

noncomputable def ForwardKernel.packageLaw (K : ForwardKernel)
    (z : ℕ → (𝓞 Fld)) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) :
    FinLaw (WalkPackage (Fld := Fld) D K.bound L) :=
  (K.law a).map (ForwardKernel.packageSymbol K z hD hs a L)

noncomputable def WalkPackage.prefix {D : ℝ} {B L : ℕ}
    (v : WalkPackage (Fld := Fld) D B L) (l : Fin L) : (𝓞 Fld) :=
  v.1.val+∑ j : Fin l.val, (v.2 ⟨j.val,lt_trans j.isLt l.isLt⟩).val

lemma ForwardKernel.packageSymbol_prefix (K : ForwardKernel)
    (z : ℕ → (𝓞 Fld)) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) (u : Fin (K.bound+1)) (l : Fin L) :
    WalkPackage.prefix (ForwardKernel.packageSymbol K z hD hs a L u) l=z (a+u.val+l.val)-z a := by
  change z (a+u.val)-z a+(∑ j : Fin l.val, incrementWord z l.val (a+u.val) j)=_
  rw [incrementWord_sum]
  abel

noncomputable def WalkPackage.Hits {D : ℝ} {B L : ℕ}
    (π : (𝓞 Fld)) (v : WalkPackage (Fld := Fld) D B L) (x : (𝓞 Fld) ⧸ multiples π) : Prop :=
  ∃ l : Fin L, ringResidue π (WalkPackage.prefix v l) = -x

lemma ForwardKernel.package_true_survives (K : ForwardKernel)
    (π : (𝓞 Fld)) (z : ℕ → (𝓞 Fld)) (havoid : ∀ t, ¬π∣z t)
    {D : ℝ} (hD : 0≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) :
    ∀ v, ForwardKernel.packageLaw K z hD hs a L v≠0 → ¬WalkPackage.Hits π v (ringResidue π (z a)) := by
  intro v hv
  rw [packageLaw,FinLaw.map_mass] at hv
  obtain ⟨u,_,hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have he : ForwardKernel.packageSymbol K z hD hs a L u=v := by
    by_contra he
    simp only [ite_eq_right he,ne_self_iff_false] at hu
  rw [← he]
  simpa only [WalkPackage.Hits,ForwardKernel.packageSymbol_prefix K] using true_residue_no_hit π z havoid a (a+u.val) L

theorem ForwardKernel.smoothed_package_floor (R : ForwardKernel)
    (π : (𝓞 Fld)) (z : ℕ → (𝓞 Fld)) (hz : Function.Injective z)
    {D τ : ℝ} (hD : 0≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    {L N : ℕ} (hshort : (D*L)^2<(integerAbsNorm Fld π:ℝ)) (hLN : L≤N)
    (herr : (L:ℝ)/(N+1)≤τ/2) (a : ℕ) (x : (𝓞 Fld) ⧸ multiples π)
    (hfloor : τ≤((R.then (smoothingKernel N)).law a).prob
      (fun u => ringResidue π (z (a+u.val)-z a) = -x)) :
    (L:ℝ)*τ/2≤(ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs a L).prob
      (fun v => WalkPackage.Hits π v x) := by
  have hf : τ≤((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => ringResidue π (z (a+v.1.val+v.2.val)-z a) = -x) := by
    change τ≤(((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).map (addOffsets R.bound N)).prob
      (fun (u : Fin (R.bound+N+1)) => ringResidue π (z (a+u.val)-z a) = -x) at hfloor
    rw [FinLaw.prob_map] at hfloor
    simpa only [addOffsets,Nat.add_assoc] using hfloor
  have hh := smoothed_package_hit_lower (R.law a) π z hz hD hs hshort hLN herr a
    (fun u => a+u.val) (-x) hf
  rw [packageLaw,FinLaw.prob_map]
  simp only [WalkPackage.Hits,packageSymbol_prefix]
  change _≤(((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).map (addOffsets R.bound N)).prob
    (fun (u : Fin (R.bound+N+1)) => ∃ l : Fin L, ringResidue π (z (a+u.val+l.val)-z a) = -x)
  rw [FinLaw.prob_map]
  simpa only [addOffsets,Nat.add_assoc] using hh

noncomputable def ForwardKernel.passingException (K : ForwardKernel)
    (s : SplitSieve Fld) (z : ℕ → (𝓞 Fld)) (a : ℕ) (i : s.SignedIndex) (τ : ℝ) :
    Finset (s.Residue i) := ((ForwardKernel.relativeResidueLaw K s z a i).lowResidues τ).image Neg.neg

omit ctx in
lemma ForwardKernel.passingException_card (K : ForwardKernel)
    (s : SplitSieve Fld) (z : ℕ → (𝓞 Fld)) (a : ℕ) (i : s.SignedIndex) (τ : ℝ) :
    (ForwardKernel.passingException K s z a i τ).card=((ForwardKernel.relativeResidueLaw K s z a i).lowResidues τ).card := by
  apply Finset.card_image_of_injective
  exact neg_injective

omit ctx in
lemma ForwardKernel.not_mem_passingException (K : ForwardKernel)
    (s : SplitSieve Fld) (z : ℕ → (𝓞 Fld)) (a : ℕ) (i : s.SignedIndex) (τ : ℝ) (x : s.Residue i)
    (hx : x∉ForwardKernel.passingException K s z a i τ) :
    τ/(s.signedPrime i:ℝ)≤(ForwardKernel.relativeResidueLaw K s z a i) (-x) := by
  have hh : -x∉(ForwardKernel.relativeResidueLaw K s z a i).lowResidues τ := by
    intro h
    exact hx (Finset.mem_image.mpr ⟨-x,h,neg_neg x⟩)
  have he := (ForwardKernel.relativeResidueLaw K s z a i).not_mem_lowResidues τ (-x) |>.mp hh
  simpa only [s.residue_card] using he

omit ctx in
lemma SplitSieve.avoids_signed (s : SplitSieve Fld) (z : (𝓞 Fld))
    (h : z∈s.avoiding) (i : s.SignedIndex) : ¬s.signedFactorAt i∣z := by
  have hh := (s.mem_avoiding z).mp h (s.signedPrime i) (s.enumeration i.2).property
  rcases i with ⟨σ,i⟩
  change ¬signedFactor _ (σ i)∣z
  cases he : σ i <;> simp only [signedFactor] <;> tauto

theorem smoothed_batch_package_information {Ω : Type uOmega} {O : Type uOutput} {ι : Type uIota}
    [Fintype Ω] [Fintype O] [Fintype ι]
    (s : SplitSieve Fld) (p : FinLaw Ω) (a : Ω → ℕ) (old : Ω → O)
    (I : ι → s.SignedIndex) (R : ForwardKernel)
    (z : ℕ → (𝓞 Fld)) (hz : Function.Injective z)
    (ha : ∀ t, z t∈s.avoiding) {D τ A H η : ℝ} {L N n : ℕ}
    (hD : 0≤D) (hτ : 0≤τ) (hA : 0≤A)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : ι → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime (I i):ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime (I i):ℝ))/2)
    (hH : (∑ i, Real.log (s.signedPrime (I i)))-H ≤
      p.cHf (fun ω i => s.residue (I i) (z (a ω))) old)
    (hBad : (∑ i, p.prob (fun ω => e i≤
      ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z (a ω) (I i)).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (4*e i+(s.signedPrime (I i):ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime (I i):ℝ))/2)/4))) ≤
        Real.log (s.signedPrime (I i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H ≤ (n:ℝ)*
      (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).cIf
        (fun v i => s.residue (I i) (z (a v.1))) Prod.snd (fun v => old v.1) := by
  let K := R.then (smoothingKernel N)
  let q := fun ω => ForwardKernel.packageLaw K z hD hs (a ω) L
  let Good := fun i ω =>
    (((ForwardKernel.relativeResidueLaw K s z (a ω) (I i)).lowResidues τ).card:ℝ)<e i
  apply FinLaw.posterior_passing_information_lower (fun i => s.Residue (I i)) p old
    (fun ω i => s.residue (I i) (z (a ω))) q (fun i => WalkPackage.Hits (s.signedFactorAt (I i)))
    Good (fun i ω => ForwardKernel.passingException K s z (a ω) (I i) τ) e
    (fun i => (L:ℝ)*(τ/(s.signedPrime (I i):ℝ))/2) n hA he
  · intro i
    positivity
  · intro ω _ v hv i
    exact ForwardKernel.package_true_survives K (s.signedFactorAt (I i)) z
      (fun t => s.avoids_signed (z t) (ha t) (I i)) hD hs (a ω) L v hv
  · intro i ω hg
    rw [ForwardKernel.passingException_card]
    exact hg.le
  · intro i ω _ x hx
    apply ForwardKernel.smoothed_package_floor R (s.signedFactorAt (I i)) z hz hD hs
      (by simpa only [s.signedFactorAt_norm] using hshort i) hLN (herr i) (a ω) x
    have hh := ForwardKernel.not_mem_passingException K s z (a ω) (I i) τ x hx
    simpa only [ForwardKernel.relativeResidueLaw,FinLaw.mass_map_eq_prob,SplitSieve.residue] using hh
  · simpa only [s.residue_card] using hH
  · simpa only [Good,not_lt] using hBad
  · simpa only [s.residue_card] using hnum

theorem ForwardKernel.package_information_transport {Ω : Type uOmega} {ι : Type uIota} {κ : Type uKappa} [Fintype Ω]
    (K : ForwardKernel) (p : FinLaw Ω) (a : Ω → ℕ) (f : ι → (𝓞 Fld)) (g : κ → (𝓞 Fld))
    (z : ℕ → (𝓞 Fld)) {D : ℝ} (hD : 1≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hK : 1≤K.bound) (L : ℕ) :
    (p.joint (fun ω => ForwardKernel.packageLaw K z (by linarith only [hD]) hs (a ω) L)).cIf
      (fun v i => residueCode (f i) (z (a v.1))) Prod.snd
      (fun v i => residueCode (g i) (z (a v.1))) ≤
    (p.joint (fun ω => K.law (a ω))).cIf
      (fun v i => residueCode (f i) (z (a v.1+v.2.val)))
      (fun v => incrementWord z L (a v.1+v.2.val))
      (fun v i => residueCode (g i) (z (a v.1+v.2.val)))+
      2*(Real.log 36+2*Real.log (D*K.bound)) := by
  let P := p.joint (fun ω => K.law (a ω))
  let X := fun v : Ω × Fin (K.bound+1) => z (a v.1)
  let Y := fun v : Ω × Fin (K.bound+1) => z (a v.1+v.2.val)
  let S := fun v => Y v-X v
  let W := fun v : Ω × Fin (K.bound+1) => incrementWord z L (a v.1+v.2.val)
  have hemap := FinLaw.joint_map_cIf p (fun ω => K.law (a ω))
    (fun ω => ForwardKernel.packageSymbol K z (by linarith only [hD]) hs (a ω) L)
    (fun ω i => residueCode (f i) (z (a ω))) (fun ω i => residueCode (g i) (z (a ω)))
  change (p.joint (fun ω => ForwardKernel.packageLaw K z (by linarith only [hD]) hs (a ω) L)).cIf _ _ _=_ at hemap
  rw [hemap]
  have he := P.cIf_congr_fibers
    (fun v i => residueCode (f i) (X v)) (fun v i => residueCode (f i) (X v))
    (fun v => ForwardKernel.packageSymbol K z (by linarith only [hD]) hs (a v.1) L v.2)
    (fun v => (S v,W v))
    (fun v i => residueCode (g i) (X v)) (fun v i => residueCode (g i) (X v))
    (fun _ _ => Iff.rfl) (fun v w => by
      simp only [ForwardKernel.packageSymbol,Prod.mk.injEq,Subtype.mk.injEq,
        ForwardKernel.displacementSymbol,boundedWord_fibers]
      rfl) (fun _ _ => Iff.rfl)
  change P.cIf _ _ _≤_
  rw [he]
  have ht := P.cIf_transport (fun v i => residueCode (f i) (X v))
    (fun v i => residueCode (g i) (X v)) (fun v i => residueCode (f i) (Y v))
    (fun v i => residueCode (g i) (Y v)) W S
    (residue_observation_shift g X Y) (by
      intro v w
      have hf := residue_observation_shift f X Y v w
      have hg := residue_observation_shift g X Y v w
      simp only [Prod.mk.injEq,S] at hf hg ⊢
      tauto)
  have hc : P.Hf S≤Real.log 36+2*Real.log (D*K.bound) := by
    apply displacement_entropy_le
    · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
    · intro v
      simpa only [S,X,Y,Nat.add_zero] using plane_walk_pair_displacement z (by linarith only [hD]) hs
        (a v.1) K.bound v.2.val 0 (by omega) (by omega)
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2 by norm_num)))

noncomputable def SplitSieve.selectedIndex (s : SplitSieve Fld) {b : ℕ} (hb : b≤ s.primes.card)
    (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) (j : Fin b) :
    s.SignedIndex := (σ,π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩)

omit ctx in
lemma SplitSieve.selected_sum_average (s : SplitSieve Fld) (hne : s.primes.Nonempty)
    {b : ℕ} (hb : b≤ s.primes.card) (f : s.SignedIndex → ℝ) :
    (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
      ∑ j : Fin b, f (s.selectedIndex hb σ π j)) =
    (b:ℝ)*(𝔼 i : s.SignedIndex, f i) := by
  have : Nonempty (Fin s.primes.card) := ⟨⟨0,hne.card_pos⟩⟩
  have hf (σ : Fin s.primes.card → Bool) (j : Fin b) :
      (𝔼 π : Equiv.Perm (Fin s.primes.card),f (s.selectedIndex hb σ π j))=
        𝔼 i : Fin s.primes.card, f (σ,i) := by
    exact perm_expect_uniform (fun i => f (σ,i)) ⟨j.val,lt_of_lt_of_le j.isLt hb⟩
  simp only [Finset.expect_sum_comm,hf,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,← Finset.mul_expect,← Finset.univ_product_univ,Finset.expect_product]

omit ctx in
lemma SplitSieve.selected_residue_fibers {Ω : Type uOmega} (s : SplitSieve Fld)
    {b : ℕ} (hb : b≤ s.primes.card) (σ : Fin s.primes.card → Bool)
    (π : Equiv.Perm (Fin s.primes.card)) (Z : Ω → (𝓞 Fld)) (ω ν : Ω) :
    (fun j => s.residue (s.selectedIndex hb σ π j) (Z ω))=
      (fun j => s.residue (s.selectedIndex hb σ π j) (Z ν)) ↔
    FinLaw.prefixVar (fun v => s.residueVector σ (Z v)) π b ω=
      FinLaw.prefixVar (fun v => s.residueVector σ (Z v)) π b ν := by
  rw [funext_iff]
  simp only [s.residue_fibers]
  change (∀ j : Fin b, s.residueVector σ (Z ω) (π ⟨j.val,_⟩)=
    s.residueVector σ (Z ν) (π ⟨j.val,_⟩)) ↔ _
  rw [← funext_iff]
  exact selected_prefix_fibers hb (fun v => s.residueVector σ (Z v)) π ω ν

omit ctx in
lemma SplitSieve.selected_entropy_average {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve Fld) (p : FinLaw Ω) (Z : Ω → (𝓞 Fld))
    {b : ℕ} (hb : b≤ s.primes.card) :
    (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
      p.Hf (fun ω j => s.residue (s.selectedIndex hb σ π j) (Z ω)))=
    s.pointEntropy p Z b := by
  have h (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :=
    p.Hf_eq_of_fibers _ _ (s.selected_residue_fibers hb σ π Z)
  simp only [h,SplitSieve.pointEntropy,FinLaw.signedEntropy,FinLaw.orderedEntropy]

omit ctx in
lemma SplitSieve.selected_log_average (s : SplitSieve Fld) (hne : s.primes.Nonempty)
    {b : ℕ} (hb : b≤ s.primes.card) :
    (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
      ∑ j : Fin b, Real.log (s.signedPrime (s.selectedIndex hb σ π j))) =
    (b:ℝ)*s.meanLog := by
  rw [s.selected_sum_average hne hb (fun i => Real.log (s.signedPrime i))]
  simp only [← Finset.univ_product_univ,Finset.expect_product,
    SplitSieve.signedPrime,Fintype.expect_const,SplitSieve.meanLog]

theorem averaged_batch_package_information {Ω : Type uOmega} {O : Type uOutput} [Fintype Ω] [Fintype O]
    (s : SplitSieve Fld) (hne : s.primes.Nonempty) (p : FinLaw Ω) (a : Ω → ℕ)
    (old : Ω → O) (R : ForwardKernel) (z : ℕ → (𝓞 Fld))
    (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    {b L N n : ℕ} (hb : b≤ s.primes.card) {D τ A η δ E : ℝ}
    (hD : 0≤D) (hτ : 0≤τ) (hA : 0≤A)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : s.SignedIndex → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy p (fun ω => z (a ω)) b)
    (hO : p.Hf old≤E)
    (hBad : (𝔼 i : s.SignedIndex, p.prob (fun ω => e i≤
      ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z (a ω) i).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (4*e i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4))) ≤
        Real.log (s.signedPrime i)-A) :
    (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E ≤ (n:ℝ)*
      (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
        (p.joint (fun ω => ForwardKernel.packageLaw (R.then (smoothingKernel N)) z hD hs (a ω) L)).cIf
          (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1)))
          Prod.snd (fun v => old v.1)) := by
  let X := fun (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card))
    (ω : Ω) (j : Fin b) => s.residue (s.selectedIndex hb σ π j) (z (a ω))
  let Bad := fun i => p.prob (fun ω => e i≤
    ((ForwardKernel.relativeResidueLaw (R.then (smoothingKernel N)) s z (a ω) i).lowResidues τ).card)
  have hi (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :=
    smoothed_batch_package_information s p a old (s.selectedIndex hb σ π) R z hz ha
      hD hτ hA hs (fun j => e (s.selectedIndex hb σ π j))
      (fun j => he _) (fun j => hshort _) hLN (fun j => herr _)
      (H := (∑ j, Real.log (s.signedPrime (s.selectedIndex hb σ π j)))-p.cHf (X σ π) old)
      (by dsimp only [X]; linarith)
      (η := ∑ j, Bad (s.selectedIndex hb σ π j)) le_rfl (fun j => hnum _)
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
  nlinarith only [hav,hxa,hH,hprod]


end QuadraticMoat
