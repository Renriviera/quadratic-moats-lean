import QuadraticMoat.TimeLaw
import OAI.NumberTheory.GaussianMoat.Information

universe uOmega uAlpha uBeta uGamma uDelta uEpsilon uZeta uIota

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]
noncomputable def differenceKernel (z : ℕ → (𝓞 Fld)) (n : ℕ) : ForwardKernel where
  bound := n
  law := fun a => ((FinLaw.uniform Bool).joint (fun _ =>
    differenceLaw (fun t => z (a+t)) n)).map (fun v => if v.1 then v.2.1 else v.2.2)

noncomputable def commonSchedule (z : ℕ → (𝓞 Fld)) (ns : List ℕ) (N : ℕ) : ForwardKernel :=
  ns.foldr (fun n K => (differenceKernel z n).then K) (smoothingKernel N)

@[simp] lemma commonSchedule_bound (z : ℕ → (𝓞 Fld)) (ns : List ℕ) (N : ℕ) :
    (commonSchedule z ns N).bound = ns.sum+N := by
  induction ns with
  | nil => simp [commonSchedule,smoothingKernel]
  | cons n ns ih =>
    change n+(commonSchedule z ns N).bound = _
    rw [ih,List.sum_cons,Nat.add_assoc]

@[simp] lemma commonSchedule_cons (z : ℕ → (𝓞 Fld)) (n : ℕ) (ns : List ℕ) (N : ℕ) :
    commonSchedule z (n::ns) N = (differenceKernel z n).then (commonSchedule z ns N) := rfl

lemma ForwardKernel.displacement_entropy (K : ForwardKernel) (a : ℕ)
    (z : ℕ → (𝓞 Fld)) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) :
    (K.law a).Hf (fun i => z (a+i.val)-z a) ≤
      Real.log 36+2*Real.log (D*K.bound) := by
  apply displacement_entropy_le
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro i
    simpa only [Nat.add_zero] using plane_walk_pair_displacement z (by linarith only [hD]) hstep
      a K.bound i.val 0 (by omega) (by omega)

lemma TimeLaw.advance_displacement_entropy (P : TimeLaw) (K : ForwardKernel)
    (z : ℕ → (𝓞 Fld)) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) :
    (P.law.joint (fun a => K.law a.val)).Hf
      (fun v => z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*K.bound) := by
  apply displacement_entropy_le
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro v
    simpa only [Nat.add_zero] using plane_walk_pair_displacement z (by linarith only [hD]) hstep
      v.1.val K.bound v.2.val 0 (by omega) (by omega)

theorem TimeLaw.step_deficit (P : TimeLaw) (s : SplitSieve Fld)
    (z : ℕ → (𝓞 Fld)) {D g e : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q : ℕ}
    (hn : 1 ≤ n) (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    (hg : 0 ≤ g) (hg1 : g ≤ 1/100) (hL : 0 ≤ s.meanLog)
    (hratio : (b:ℝ) ≤ g*q)
    (hfresh : ∀ a : Fin (P.last+1), (1-30*g)*s.meanLog ≤ s.freshCoordinate
      (differenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) b (by omega))
    (hE : (1-e)*(q:ℝ)*s.meanLog ≤ s.pointEntropy P.law (fun a => z a.val) q)
    (hcost : 2*(Real.log 36+2*Real.log (D*n)) ≤ 8*g*q*s.meanLog) :
    (1-e/2-20*g)*(b:ℝ)*s.meanLog ≤
      s.pointEntropy (P.step z n).law (fun a => z a.val) b := by
  exact entropy_step_deficit (by omega) hL hg hg1 hratio le_rfl hE hcost
    (P.step_enrichment s z hD hstep hn hb hbq hq hfresh)

lemma TimeLaw.advance_difference (P : TimeLaw) (z : ℕ → (𝓞 Fld)) (n : ℕ) :
    P.advance (differenceKernel z n) = P.step z n := by
  unfold TimeLaw.advance TimeLaw.step differenceKernel
  congr 1
  dsimp only
  rw [FinLaw.joint_observation_fun]
  conv_lhs => arg 2; ext a; rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  rw [FinLaw.mix_comm,FinLaw.joint_observation_fun]
  conv_rhs => arg 2; ext c; rw [FinLaw.joint_observation_fun]
  apply congrArg
  funext c
  apply congrArg
  funext a
  apply congrArg
  funext ij
  apply Fin.ext
  dsimp only [Function.comp_def,addOffsets,endpointTime]
  split_ifs <;> rfl
theorem SplitSieve.pointEntropy_shift {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve Fld) (p : FinLaw Ω) (X Y : Ω → (𝓞 Fld)) (b : ℕ) :
    s.pointEntropy p X b ≤ s.pointEntropy p Y b+p.Hf (fun ω => Y ω-X ω) := by
  have h (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      p.Hf (FinLaw.prefixVar (fun ω => s.residueVector σ (X ω)) π b) ≤
        p.Hf (FinLaw.prefixVar (fun ω => s.residueVector σ (Y ω)) π b)+
          p.Hf (fun ω => Y ω-X ω) := by
    apply (p.Hf_le_of_determined _ (fun ω =>
      (FinLaw.prefixVar (fun ν => s.residueVector σ (Y ν)) π b ω,Y ω-X ω)) ?_).trans
      (p.Hf_pair_subadd _ _)
    intro ω ν hh
    funext i
    by_cases hi : i.val<b
    · have hy : s.residueVector σ (Y ω) (π i)=s.residueVector σ (Y ν) (π i) := by
        simpa [FinLaw.prefixVar,hi] using congrFun (congrArg Prod.fst hh) i
      have hd := congrArg (residueCode (signedFactor (s.factor (s.enumeration (π i))) (σ (π i)))) (congrArg Prod.snd hh)
      have hx := residueCode_sub hy hd
      simpa only [sub_sub_cancel,SplitSieve.residueVector,FinLaw.prefixVar,hi,ite_eq_left]
        using congrArg some hx
    · simp [FinLaw.prefixVar,hi]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => h σ π))
  simpa only [SplitSieve.pointEntropy,FinLaw.signedEntropy,FinLaw.orderedEntropy,
    Finset.expect_add_distrib,Fintype.expect_const] using hh

lemma residue_observation_shift {Ω : Type uOmega} {ι : Type uIota} (f : ι → (𝓞 Fld))
    (X Y : Ω → (𝓞 Fld)) (ω ν : Ω) :
    ((fun i => residueCode (f i) (X ω)),Y ω-X ω)=
      ((fun i => residueCode (f i) (X ν)),Y ν-X ν) ↔
    ((fun i => residueCode (f i) (Y ω)),Y ω-X ω)=
      ((fun i => residueCode (f i) (Y ν)),Y ν-X ν) := by
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hx,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h := residueCode_add (congrFun hx i) (congrArg (residueCode (f i)) hd)
    simpa only [add_sub_cancel] using h
  · rintro ⟨hy,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h := residueCode_sub (congrFun hy i) (congrArg (residueCode (f i)) hd)
    simpa only [sub_sub_cancel] using h

end QuadraticMoat
