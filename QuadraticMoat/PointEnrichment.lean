import QuadraticMoat.FreshEntropy
import QuadraticMoat.PlaneLattice
import OAI.NumberTheory.GaussianMoat.PointEnrichment

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
universe uOmega uIota uCapitalKappa
variable {K : Type*} [Field K] [NumberField K] [ctx : PlanarContext K]

noncomputable abbrev walkSegment := integerWalkSegment (K := K)
noncomputable abbrev differences := integerDifferences (K := K)

omit [NumberField K] ctx in
@[simp] lemma mem_walkSegment (z : ℕ → 𝓞 K) (n : ℕ) (w : 𝓞 K) :
    w ∈ walkSegment z n ↔ ∃ i ≤ n, z i = w := mem_integerWalkSegment z n w
omit [NumberField K] ctx in
@[simp] lemma mem_differences (E : Finset (𝓞 K)) (w : 𝓞 K) :
    w ∈ differences E ↔ ∃ a ∈ E, ∃ b ∈ E, a-b = w := mem_integerDifferences E w

theorem displacement_entropy_le {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (Z : Ω → 𝓞 K) {R : ℝ} (hR : 1 ≤ R) (hZ : ∀ ω, ‖(Z ω:ℂ)‖ ≤ R) :
    p.Hf Z ≤ Real.log 36+2*Real.log R := by
  rw [p.Hf_eq_of_fibers Z (fun ω => coordinateGaussian ctx.basis (Z ω))
    (fun ω ν => (coordinateGaussian ctx.basis).injective.eq_iff.symm)]
  exact OAI.GaussianMoat.displacement_entropy_le p _ hR
    (fun ω => (coordinate_norm_le_plane (Z ω)).trans (hZ ω))

theorem differences_rectangle (E : Finset (𝓞 K)) {e c : ℂ} {R W : ℝ}
    (hE : ∀ p ∈ E, 0 ≤ (e*((p:ℂ)-c)).re ∧
      (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W) :
    ∀ x ∈ differences E, ∀ y ∈ differences E,
      x-y ∈ orientedRectangle ctx.basis ctx.scale (star e) (4*R) (4*W) := by
  intro x hx y hy
  obtain ⟨a,ha,b,hb,rfl⟩ := (mem_differences E x).mp hx
  obtain ⟨a',ha',b',hb',rfl⟩ := (mem_differences E y).mp hy
  have h1 := hE a ha
  have h2 := hE b hb
  have h3 := hE a' ha'
  have h4 := hE b' hb'
  have heq : e*((a:ℂ)-(b:ℂ)-((a':ℂ)-(b':ℂ))) =
      e*((a:ℂ)-c)-e*((b:ℂ)-c)-(e*((a':ℂ)-c)-e*((b':ℂ)-c)) := by ring
  rw [orientedRectangle]
  change |(star (star e) * ((a-b-(a'-b') : 𝓞 K) : ℂ)).re| ≤ 4*R ∧
    |(star (star e) * ((a-b-(a'-b') : 𝓞 K) : ℂ)).im| ≤ 4*W
  simp only [star_star,toPlane_sub,heq,Complex.sub_re,Complex.sub_im]
  obtain ⟨h1i,h1i'⟩ := abs_le.mp h1.2.2
  obtain ⟨h2i,h2i'⟩ := abs_le.mp h2.2.2
  obtain ⟨h3i,h3i'⟩ := abs_le.mp h3.2.2
  obtain ⟨h4i,h4i'⟩ := abs_le.mp h4.2.2
  refine ⟨abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith

omit [NumberField K] ctx in
lemma difference_exists_pair (z : ℕ → (𝓞 K)) (n : ℕ)
    (d : differences (walkSegment z n)) :
    ∃ ij : Fin (n+1) × Fin (n+1), z ij.1.val-z ij.2.val=d := by
  obtain ⟨a,ha,b,hb,hab⟩ := (mem_differences _ _).mp d.property
  obtain ⟨i,hi,rfl⟩ := (mem_walkSegment _ _ _).mp ha
  obtain ⟨j,hj,rfl⟩ := (mem_walkSegment _ _ _).mp hb
  exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hab⟩

noncomputable def differenceRepresentative (z : ℕ → (𝓞 K)) (n : ℕ)
    (d : differences (walkSegment z n)) : Fin (n+1) × Fin (n+1) :=
  (difference_exists_pair z n d).choose

omit [NumberField K] ctx in
lemma differenceRepresentative_spec (z : ℕ → (𝓞 K)) (n : ℕ)
    (d : differences (walkSegment z n)) :
    z (differenceRepresentative z n d).1.val-z (differenceRepresentative z n d).2.val=d :=
  (difference_exists_pair z n d).choose_spec

omit [NumberField K] ctx in
lemma differenceRepresentative_injective (z : ℕ → (𝓞 K)) (n : ℕ) :
    Function.Injective (differenceRepresentative z n) := by
  intro d d' hh
  apply Subtype.ext
  rw [← differenceRepresentative_spec z n d,← differenceRepresentative_spec z n d',hh]

omit [NumberField K] ctx in
lemma differences_walkSegment_nonempty (z : ℕ → (𝓞 K)) (n : ℕ) :
    (differences (walkSegment z n)).Nonempty := by
  refine ⟨0,(mem_differences _ _).mpr ⟨z 0,?_,z 0,?_,sub_self _⟩⟩ <;>
    exact (mem_walkSegment _ _ _).mpr ⟨0,by omega,rfl⟩


noncomputable def SplitSieve.pointEntropy {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve K) (P : FinLaw Ω) (Z : Ω → (𝓞 K)) (b : ℕ) : ℝ :=
  P.signedEntropy (fun σ ω => s.residueVector σ (Z ω)) b

noncomputable def SplitSieve.freshCoordinate {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve K) (P : FinLaw Ω) (X Y : Ω → (𝓞 K))
    (b : ℕ) (hb : b < s.primes.card) : ℝ :=
  𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
    P.cHf (fun ω => s.residueVector σ (X ω-Y ω) (π ⟨b,hb⟩))
      (fun ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X x)) π b ω,
        FinLaw.prefixVar (fun x => s.residueVector σ (Y x)) π b ω))

omit ctx in
lemma SplitSieve.freshCoordinate_map {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve K) (p : FinLaw Ω) (f : Ω → Κ) (X Y : Κ → (𝓞 K))
    (b : ℕ) (hb : b < s.primes.card) :
    s.freshCoordinate (p.map f) X Y b hb = s.freshCoordinate p (X ∘ f) (Y ∘ f) b hb := by
  unfold SplitSieve.freshCoordinate
  simp only [FinLaw.cHf_map,Function.comp_def]
  rfl

noncomputable def differenceLaw (z : ℕ → (𝓞 K)) (n : ℕ) :
    FinLaw (Fin (n+1) × Fin (n+1)) := by
  let := (differences_walkSegment_nonempty z n).to_subtype
  exact (FinLaw.uniform (differences (walkSegment z n))).map (differenceRepresentative z n)

theorem differenceLaw_fresh (s : SplitSieve K) (z : ℕ → (𝓞 K)) (n : ℕ)
    {b r : ℕ} (hbr : b < r) (hr : r ≤ s.primes.card)
    {T R W d δ : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log (R*W) ≤ (1-d)*(r*s.meanLog-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ differences (walkSegment z n), ∀ y ∈ differences (walkSegment z n),
      x-y ∈ orientedRectangle ctx.basis ctx.scale e R W) :
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*
        Real.log (differences (walkSegment z n)).card-2*b*Real.log (2*T) ≤
      (r-b : ℕ)*s.freshCoordinate (differenceLaw z n)
        (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega) := by
  let Δ := differences (walkSegment z n)
  let hne := differences_walkSegment_nonempty z n
  let := hne.to_subtype
  let X : Δ → (𝓞 K) := fun ω => z (differenceRepresentative z n ω).1.val
  let Y : Δ → (𝓞 K) := fun ω => z (differenceRepresentative z n ω).2.val
  have hXY : ∀ ω, X ω-Y ω=ω := differenceRepresentative_spec z n
  have h := s.actual_fresh_entropy (ctx := ctx) hbr hr Δ hne X Y hXY he hT hpT hW hWR hd hd1 hδ hgap hlarge hΔ
  change _ ≤ (r-b : ℕ)*s.freshCoordinate
    ((FinLaw.uniform Δ).map (differenceRepresentative z n))
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega)
  rw [s.freshCoordinate_map]
  change _ ≤ (r-b : ℕ)*s.freshCoordinate (FinLaw.uniform Δ) X Y b (by omega)
  simpa only [SplitSieve.freshCoordinate,hXY] using h

omit ctx in
theorem SplitSieve.freshCoordinate_joint_ge {ι : Type uIota} {Ω : Type uOmega} [Fintype ι] [Fintype Ω]
    (s : SplitSieve K) (p : FinLaw ι) (q : ι → FinLaw Ω)
    (X Y : ι → Ω → (𝓞 K)) {b : ℕ} (hb : b < s.primes.card) :
    (∑ i, p i*s.freshCoordinate (q i) (X i) (Y i) b hb) ≤
      s.freshCoordinate (p.joint q) (fun v => X v.1 v.2) (fun v => Y v.1 v.2) b hb := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
      p.cHf_joint_ge q (fun i ω => s.residueVector σ (X i ω-Y i ω) (π ⟨b,hb⟩))
        (fun i ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X i x)) π b ω,
          FinLaw.prefixVar (fun x => s.residueVector σ (Y i x)) π b ω))))
  simpa only [SplitSieve.freshCoordinate,Finset.expect_sum_comm,Finset.mul_expect] using! h

omit ctx in
lemma pointEntropy_fair_endpoint {Ω : Type uOmega} [Fintype Ω] (s : SplitSieve K)
    (p : FinLaw Ω) (X Y : Ω → (𝓞 K)) (b : ℕ) :
    s.pointEntropy p X b+s.pointEntropy p Y b ≤
      2*s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => p))
        (fun v => if v.1 then X v.2 else Y v.2) b := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
      (FinLaw.uniform Bool).Hf_joint_ge (fun _ => p)
        (fun c ω => FinLaw.prefixVar (fun x => s.residueVector σ (if c then X x else Y x)) π b ω)))
  simp only [Fintype.sum_bool,FinLaw.uniform_mass,Fintype.card_bool,Nat.cast_ofNat,
    Bool.false_eq_true,ite_false,ite_true,Finset.expect_add_distrib,← Finset.mul_expect] at h
  change (2:ℝ)⁻¹*s.pointEntropy p X b+(2:ℝ)⁻¹*s.pointEntropy p Y b ≤
    s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => p))
      (fun v => if v.1 then X v.2 else Y v.2) b at h
  linarith

omit ctx in
theorem SplitSieve.point_enrichment_accounting {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve K) (p : FinLaw Ω) (X Y Z : Ω → (𝓞 K))
    {b q : ℕ} (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card) :
    (b : ℝ)*((q-b : ℕ)*s.freshCoordinate p X Y b (by omega)+
      s.pointEntropy p Z q-p.Hf (fun ω => X ω-Y ω)-p.Hf (fun ω => X ω-Z ω)) ≤
      (q : ℝ)*(s.pointEntropy p X b+s.pointEntropy p Y b) := by
  have h (σ : Fin s.primes.card → Bool) := p.ordered_enrichment_accounting
    (fun ω => s.residueVector σ (X ω)) (fun ω => s.residueVector σ (Y ω))
    (fun ω => s.residueVector σ (Z ω)) (fun ω => s.residueVector σ (X ω-Y ω))
    (fun ω => X ω-Y ω) (fun ω => X ω-Z ω) hb hbq hq
    (by intro i ω ν hx hy; exact residueCode_sub hx hy)
    (by
      intro i ω ν hx hd
      have h := residueCode_sub hx hd
      simpa only [sub_sub_cancel,SplitSieve.residueVector] using h)
    (by intro i ω ν hh; rw [hh])
    (by
      intro i ω ν hx he
      have h := residueCode_sub hx (congrArg (residueCode _) he)
      simpa only [sub_sub_cancel,SplitSieve.residueVector] using h)
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => h σ)
  simpa only [SplitSieve.pointEntropy,FinLaw.signedEntropy,SplitSieve.freshCoordinate,
    Finset.expect_sub_distrib,Finset.expect_add_distrib,← Finset.mul_expect,Fintype.expect_const] using hh

theorem SplitSieve.actual_enrichment {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve K) (p : FinLaw Ω) (X Y Z : Ω → (𝓞 K))
    {b q : ℕ} (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    {F R : ℝ} (hF : F ≤ s.freshCoordinate p X Y b (by omega))
    (hR : 1 ≤ R) (hXY : ∀ ω, ‖((X ω-Y ω:(𝓞 K)):ℂ)‖ ≤ R)
    (hXZ : ∀ ω, ‖((X ω-Z ω:(𝓞 K)):ℂ)‖ ≤ R) :
    (b : ℝ)*((q-b : ℕ)*F+s.pointEntropy p Z q-2*(Real.log 36+2*Real.log R)) ≤
      2*(q : ℝ)*s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => p))
        (fun v => if v.1 then X v.2 else Y v.2) b := by
  have hc := s.point_enrichment_accounting p X Y Z hb hbq hq
  have h1 := displacement_entropy_le p (fun ω => X ω-Y ω) hR hXY
  have h2 := displacement_entropy_le p (fun ω => X ω-Z ω) hR hXZ
  have he := pointEntropy_fair_endpoint s p X Y b
  have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg q)
  have hf := mul_le_mul_of_nonneg_left hF (show (0:ℝ) ≤ (q-b:ℕ) by positivity)
  have hsub : (q-b:ℕ)*F+s.pointEntropy p Z q-2*(Real.log 36+2*Real.log R) ≤
      (q-b:ℕ)*s.freshCoordinate p X Y b (by omega)+s.pointEntropy p Z q-
        p.Hf (fun ω => X ω-Y ω)-p.Hf (fun ω => X ω-Z ω) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg b)
  nlinarith

open scoped BigOperators Classical

lemma fresh_error_bounds {g L r : ℝ} (hg : 0 < g) (hg1 : g ≤ 1/100)
    (hL : 1 ≤ L) (hr : 0 < r) (hlarge : 5120 ≤ g^4*r) :
    r*(Real.log 2)^2/(2*g*r*L)^2 ≤ g ∧ Real.exp (-(g^3*r/5120)) ≤ g := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hl2 : (Real.log 2)^2 ≤ 1 := by nlinarith
  have hg4 : 0 < g^4 := pow_pos hg _
  have hg3 : 0 < g^3 := pow_pos hg _
  have hgL : 0 < 2*g*r*L := by positivity
  have hgr : 1 ≤ g^3*r := by
    have h : g^4*r = g*(g^3*r) := by ring
    have hp : 0 ≤ g^3*r := mul_nonneg hg3.le hr.le
    nlinarith
  have hLL : 1 ≤ L^2 := by nlinarith
  have hprod := mul_le_mul hgr hLL (by norm_num : (0:ℝ)≤1) (mul_nonneg hg3.le hr.le)
  have hrr : 0 ≤ r*(4*(g^3*r*L^2)-1) := mul_nonneg hr.le (by nlinarith)
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hgL)).mpr
    have h := mul_le_mul_of_nonneg_left hl2 hr.le
    nlinarith
  · have hpow : 1/g ≤ g^3*r/5120 := by
      apply (div_le_iff₀ hg).mpr
      nlinarith
    have hlogg : -(1/g) ≤ Real.log g := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hg)
      rw [Real.log_inv] at h
      simp only [one_div] at h ⊢
      linarith
    exact (Real.exp_le_exp.mpr (by linarith : -(g^3*r/5120) ≤ Real.log g)).trans_eq
      (Real.exp_log hg)

lemma fresh_gap_bound {g a L r : ℝ} (hg : 0 < g) (hg1 : g ≤ 1/100)
    (ha : 0 ≤ a) (hlow : (1+10*g)*a ≤ r*L) :
    a ≤ (1-g)*(r*L-2*g*r*L) := by
  have hfac : 0 ≤ (1-g)*(1-2*g) := mul_nonneg (by linarith) (by linarith)
  have h := mul_le_mul_of_nonneg_left hlow hfac
  have hn : 0 ≤ g*(7-30*g) := mul_nonneg hg.le (by linarith)
  have he : 1 ≤ (1-g)*(1-2*g)*(1+10*g) := by
    have hg3 : 0 ≤ g^3 := pow_nonneg hg.le _
    nlinarith
  have ha' := mul_le_mul_of_nonneg_right he ha
  nlinarith

theorem SplitSieve.differenceLaw_fresh_lower (s : SplitSieve K)
    (z : ℕ → (𝓞 K)) (n : ℕ) {b r : ℕ}
    (hbr : b < r) (hr : r ≤ s.primes.card)
    {T R W g a : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hg : 0 < g) (hg1 : g ≤ 1/100)
    (hmean : 1 ≤ s.meanLog) (ha : a = Real.log (R*W)) (ha0 : 0 ≤ a)
    (hlow : (1+10*g)*a ≤ r*s.meanLog) (hhigh : r*s.meanLog ≤ (1+11*g)*a)
    (hlarge : 5120 ≤ g^4*r)
    (hsize : (1-g)*a ≤ Real.log (differences (walkSegment z n)).card)
    (hcost : 2*b*Real.log (2*T) ≤ 8*g*a)
    (hΔ : ∀ x ∈ differences (walkSegment z n), ∀ y ∈ differences (walkSegment z n),
      x-y ∈ orientedRectangle ctx.basis ctx.scale e R W) :
    (1-30*g)*s.meanLog ≤ s.freshCoordinate (differenceLaw z n)
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hg14 : g < 1/4 := by linarith
  have hδ : 0 < 2*g*r*s.meanLog := by positivity
  have hgap : Real.log (R*W) ≤ (1-g)*(r*s.meanLog-2*g*r*s.meanLog) := by
    rw [← ha]
    exact fresh_gap_bound hg hg1 ha0 hlow
  have hlarge' : 1000 ≤ g^3*(r:ℝ) := by
    have hp : 0 ≤ g^3*(r:ℝ) := by positivity
    have hid : g^4*(r:ℝ) = g*(g^3*r) := by ring
    nlinarith
  have herr := fresh_error_bounds hg hg1 hmean hr0 hlarge
  have h := differenceLaw_fresh s z n hbr hr he hT hpT hW hWR hg hg14 hδ
    hgap hlarge' hΔ
  have hsize0 : 0 ≤ Real.log (differences (walkSegment z n)).card := by
    have hh : 0 ≤ (1-g)*a := mul_nonneg (by linarith) ha0
    linarith
  have he := mul_le_mul_of_nonneg_right (show 1-2*g ≤
      1-(r:ℝ)*(Real.log 2)^2/(2*g*r*s.meanLog)^2-
        Real.exp (-(g^3*r/5120)) by linarith [herr.1,herr.2]) hsize0
  have hs := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 1-2*g by linarith)
  have hnum : (1-11*g)*a ≤ (r-b:ℕ)*s.freshCoordinate (differenceLaw z n)
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega) := by
    have hx : 0 ≤ 2*g^2*a := by positivity
    nlinarith
  have hp0 : 0 ≤ 1-30*g := by linarith
  have hh := mul_le_mul_of_nonneg_left hhigh hp0
  have hh2 : (1-30*g)*((1+11*g)*a) ≤ (1-11*g)*a := by
    have h1 : 0 ≤ g*a := mul_nonneg hg.le ha0
    have h2 : 0 ≤ g^2*a := mul_nonneg (sq_nonneg _) ha0
    nlinarith
  have hbrR : (r-b:ℕ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r b
  have hb0 : (0:ℝ) < (r-b:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hbr
  have hm := mul_le_mul_of_nonneg_right hbrR (mul_nonneg hp0 (by linarith : 0 ≤ s.meanLog))
  nlinarith

omit ctx in
lemma SplitSieve.meanLog_bounds (s : SplitSieve K) (hne : s.primes.Nonempty) {T : ℝ}
    (hT : 0 < T) (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T) :
    Real.log T ≤ s.meanLog ∧ s.meanLog ≤ Real.log (2*T) := by
  have : Nonempty (Fin s.primes.card) := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hne)
  constructor
  · have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      Real.log_le_log hT (hpT _ (s.enumeration i).property).1)
    simpa only [SplitSieve.meanLog,Fintype.expect_const] using h
  · apply Finset.expect_le (Finset.univ_nonempty)
    intro i _
    exact Real.log_le_log (lt_of_lt_of_le hT (hpT _ (s.enumeration i).property).1)
      (hpT _ (s.enumeration i).property).2

theorem SplitSieve.walk_fresh_lower (s : SplitSieve K) (hne : s.primes.Nonempty)
    (z : ℕ → (𝓞 K)) {n : ℕ} (hn : 1 ≤ n) (hinj : Function.Injective z)
    {D T g : ℝ} (hD : 1 ≤ D) (hDscale : ctx.scale ≤ D) (hT : 5 ≤ T)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog)
    {b : ℕ} (hu : 0 < Real.log n-Real.log 18)
    (hround : s.meanLog ≤ g*(Real.log n-Real.log 18))
    (hlarge : 5120*s.meanLog ≤ g^4*(Real.log n-Real.log 18))
    (hcost : (b:ℝ)*s.meanLog ≤ g*(Real.log n-Real.log 18))
    (hsize : Real.log 16+Real.log (ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ)) ≤
      g*(Real.log n-Real.log 18))
    (hcap : 2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*s.meanLog) :
    ∃ hb : b < s.primes.card,
      (1-30*g)*s.meanLog ≤ s.freshCoordinate (differenceLaw z n)
        (fun ij => z ij.1.val) (fun ij => z ij.2.val) b hb := by
  have hscale0 : 0 < ctx.scale := by linarith [ctx.scale_ge_one]
  have hcoordD : 1 ≤ D/ctx.scale := (le_div_iff₀ hscale0).mpr (by simpa using hDscale)
  have hcoord : ∀ i < n, dist (coordinateComplex ctx.basis (z i))
      (coordinateComplex ctx.basis (z (i+1))) ≤ D/ctx.scale := by
    intro i hi
    have hzi := hz i hi
    have hdist : dist (z i : ℂ) (z (i+1) : ℂ) =
        ctx.scale * dist (coordinateComplex ctx.basis (z i))
          (coordinateComplex ctx.basis (z (i+1))) := by
      change dist (scaledCoordinateComplex ctx.basis ctx.scale (z i))
        (scaledCoordinateComplex ctx.basis ctx.scale (z (i+1))) = _
      simp only [scaledCoordinateComplex, dist_eq_norm, ← mul_sub, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale0]
    rw [hdist] at hzi
    exact (le_div_iff₀ hscale0).mpr (by simpa only [mul_comm] using hzi)
  obtain ⟨R,W,e,c,hW,hWR,he,hrect,hnA,hAup,hAΔ⟩ :=
    scaled_walk_many_differences ctx.basis ctx.scale ctx.scale_ge_one z hn hinj hcoordD hcoord
  rw [mul_div_cancel₀ _ hscale0.ne'] at hAup
  have hRp : 0 < R := by linarith
  have hWp : 0 < W := by linarith
  have hA : 0 < R*W := mul_pos hRp hWp
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hLp : 0 < s.meanLog := by linarith
  let a := Real.log (16*(R*W))
  let u := Real.log n-Real.log 18
  have hua : u ≤ a := by
    have h := Real.log_le_log hnR hnA
    rw [Real.log_mul (by norm_num : (18:ℝ)≠0) hA.ne'] at h
    have hl16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    dsimp [u,a]
    rw [Real.log_mul (by norm_num : (16:ℝ)≠0) hA.ne']
    linarith
  have ha0 : 0 < a := lt_of_lt_of_le hu hua
  have hav : a ≤ 2*Real.log n+Real.log 16+2*Real.log D := by
    have h := Real.log_le_log hA hAup
    rw [Real.log_mul (pow_ne_zero _ (by linarith : D≠0)) (pow_ne_zero _ hnR.ne'),
      Real.log_pow,Real.log_pow] at h
    dsimp [a]
    rw [Real.log_mul (by norm_num : (16:ℝ)≠0) hA.ne']
    norm_num at h
    linarith only [h]
  let r := ⌈(1+10*g)*a/s.meanLog⌉₊
  have hlo : (1+10*g)*a ≤ (r:ℝ)*s.meanLog := by
    exact (div_le_iff₀ hLp).mp (Nat.le_ceil _)
  have hhi : (r:ℝ)*s.meanLog ≤ (1+11*g)*a := by
    have hx : 0 ≤ (1+10*g)*a/s.meanLog := by positivity
    have hc := Nat.ceil_lt_add_one hx
    have hh := mul_lt_mul_of_pos_right hc hLp
    have heq : ((1+10*g)*a/s.meanLog+1)*s.meanLog = (1+10*g)*a+s.meanLog := by
      rw [add_mul,div_mul_cancel₀ _ hLp.ne',one_mul]
    rw [heq] at hh
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    change (r:ℝ)*s.meanLog < (1+10*g)*a+s.meanLog at hh
    nlinarith only [hh,hround,hgu]
  have hr : r ≤ s.primes.card := by
    suffices hh : (r:ℝ) ≤ s.primes.card by exact_mod_cast hh
    have hh : (1+11*g)*a ≤ 2*a := by nlinarith only [hg1,ha0]
    nlinarith only [hhi,hh,hav,hcap,hLp]
  have hbr : b < r := by
    suffices hh : (b:ℝ) < r by exact_mod_cast hh
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    nlinarith only [hcost,hgu,hlo,hg1,hLp,ha0]
  have hlr : 5120 ≤ g^4*(r:ℝ) := by
    have hg4 : 0 < g^4 := pow_pos hg _
    have h1 : u ≤ (r:ℝ)*s.meanLog := by nlinarith only [hlo,hua,hg,ha0]
    have h2 := mul_le_mul_of_nonneg_left h1 hg4.le
    nlinarith only [h2,hlarge,hLp]
  have hC : 0 < ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ) :=
    mul_pos (sq_pos_of_pos (by linarith [ctx.scale_ge_one]))
      (lt_of_lt_of_le (by linarith : 0 < D/ctx.scale) (le_max_left _ _))
  have hdc : (0:ℝ) < (differences (walkSegment z n)).card := by
    exact_mod_cast Finset.card_pos.mpr (differences_walkSegment_nonempty z n)
  have hsz : (1-g)*a ≤ Real.log (differences (walkSegment z n)).card := by
    have h := Real.log_le_log hA hAΔ
    rw [Real.log_mul hC.ne' hdc.ne'] at h
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    have haeq : a = Real.log 16+Real.log (R*W) := by
      exact Real.log_mul (by norm_num) hA.ne'
    nlinarith only [h,hgu,haeq,hsize]
  have hlog2 : Real.log (2*T) ≤ 2*s.meanLog := by
    have hm := s.meanLog_bounds hne (by linarith) hpT
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith : T≠0)]
    linarith only [hm.1,hlog2,hL]
  have hbc : 2*(b:ℝ)*Real.log (2*T) ≤ 8*g*a := by
    have h := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0:ℝ)≤2*b)
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    have hga : 0 ≤ g*a := by positivity
    nlinarith only [h,hgu,hcost,hga]
  refine ⟨by omega,?_⟩
  apply s.differenceLaw_fresh_lower z n hbr hr (e := star e) (R := 4*R) (W := 4*W)
    (by simpa using he) hT hpT (by linarith) (by linarith) hg hg1 hL
    (a := a) (by dsimp [a]; congr 1; ring) ha0.le hlo hhi hlr hsz hbc
  exact differences_rectangle (walkSegment z n) hrect


end QuadraticMoat
