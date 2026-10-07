import QuadraticMoat.PointEnrichment
import OAI.NumberTheory.GaussianMoat.SignedResidues

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
universe uOmega uAlpha
variable {K : Type*} [Field K] [NumberField K]

theorem SplitSieve.coverage_conditioning {Ω : Type uOmega} {β : Type*} [Fintype Ω]
    (s : SplitSieve K) (p : FinLaw Ω) (Y : Ω → 𝓞 K) (C : Ω → β)
    {b : ℕ} (hb : b ≤ s.primes.card) :
    s.pointEntropy p Y b-p.Hf C ≤
      b*(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
        p.cHf (fun ω => s.residueVector σ (Y ω) i) C) :=
  p.signedEntropy_conditioning _ C hb

abbrev SplitSieve.SignedIndex (s : SplitSieve K) := (Fin s.primes.card → Bool) × Fin s.primes.card

noncomputable def SplitSieve.signedPrime (s : SplitSieve K) (i : s.SignedIndex) : ℕ :=
  s.enumeration i.2
noncomputable def SplitSieve.signedFactorAt (s : SplitSieve K) (i : s.SignedIndex) : (𝓞 K) :=
  signedFactor (s.factor (s.signedPrime i)) (i.1 i.2)

lemma SplitSieve.signedFactorAt_norm (s : SplitSieve K) (i : s.SignedIndex) :
    integerAbsNorm K (s.signedFactorAt i) = s.signedPrime i :=
  s.signedFactor_norm _ (s.enumeration i.2).property _

lemma SplitSieve.signedFactorAt_ne_zero (s : SplitSieve K) (i : s.SignedIndex) :
    s.signedFactorAt i ≠ 0 := (s.signedFactor_prime _ (s.enumeration i.2).property _).ne_zero

abbrev SplitSieve.Residue (s : SplitSieve K) (i : s.SignedIndex) :=
  (𝓞 K) ⧸ multiples (s.signedFactorAt i)
noncomputable instance SplitSieve.residueFintype (s : SplitSieve K) (i : s.SignedIndex) :
    Fintype (s.Residue i) := by
  let := finite_ringResidue (s.signedFactorAt_ne_zero i)
  exact Fintype.ofFinite _

lemma SplitSieve.residue_card (s : SplitSieve K) (i : s.SignedIndex) :
    Fintype.card (s.Residue i)=s.signedPrime i := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ((𝓞 K) ⧸ multiples (s.signedFactorAt i)) = _
  rw [multiples_index,s.signedFactorAt_norm]

noncomputable def SplitSieve.residue (s : SplitSieve K) (i : s.SignedIndex) :
    (𝓞 K) → s.Residue i := ringResidue (s.signedFactorAt i)

lemma SplitSieve.residue_fibers (s : SplitSieve K) (i : s.SignedIndex) (z w : (𝓞 K)) :
    s.residue i z=s.residue i w ↔ s.residueVector i.1 z i.2=s.residueVector i.1 w i.2 := by
  change ringResidue _ z=ringResidue _ w ↔ residueCode _ z=residueCode _ w
  rw [ringResidue_eq,residueCode_eq]
  rfl

lemma SplitSieve.signedIndex_nonempty (s : SplitSieve K) (hne : s.primes.Nonempty) :
    Nonempty s.SignedIndex := by
  have hk := hne.card_pos
  exact ⟨(fun _ => true,⟨0,hk⟩)⟩

theorem SplitSieve.signed_coverage_deficit {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω]
    (s : SplitSieve K) (hne : s.primes.Nonempty) (p : FinLaw Ω)
    (Z : Ω → (𝓞 K)) (C : Ω → α) (a : (𝓞 K)) {b : ℕ}
    (hb : 0<b) (hbk : b ≤ s.primes.card) {e E : ℝ}
    (hH : (1-e)*(b:ℝ)*s.meanLog ≤ s.pointEntropy p Z b)
    (hC : p.Hf C≤E) :
    letI := s.signedIndex_nonempty hne
    (∑ i : s.SignedIndex, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      p.cHf (fun ω => s.residue i (Z ω-a)) C)) ≤ e*s.meanLog+E/b := by
  let := s.signedIndex_nonempty hne
  have hc := s.coverage_conditioning p Z C hbk
  have he (i : s.SignedIndex) :
      p.cHf (fun ω => s.residue i (Z ω-a)) C =
        p.cHf (fun ω => s.residueVector i.1 (Z ω) i.2) C := by
    apply p.cHf_congr_fibers _ _ _ _
    · intro ω ν
      change ringResidue _ (Z ω-a)=ringResidue _ (Z ν-a) ↔ _
      rw [ringResidue_sub,ringResidue_sub,sub_left_inj]
      exact s.residue_fibers i _ _
    · intro ω ν; rfl
  have hd : (∑ i : s.SignedIndex, FinLaw.uniform _ i*
      (Real.log (Fintype.card (s.Residue i))-p.cHf (fun ω => s.residue i (Z ω-a)) C)) =
      s.meanLog-(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
        p.cHf (fun ω => s.residueVector σ (Z ω) i) C) := by
    rw [FinLaw.uniform_expect]
    simp only [s.residue_card,he,Finset.expect_sub_distrib]
    simp only [← Finset.univ_product_univ,Finset.expect_product]
    simp only [signedPrime,meanLog,Fintype.expect_const]
  rw [hd]
  have hbp : (0:ℝ)<b := by exact_mod_cast hb
  apply (mul_le_mul_iff_left₀ hbp).mp
  have hgoal : (s.meanLog-(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
      p.cHf (fun ω => s.residueVector σ (Z ω) i) C))*(b:ℝ) ≤
        (e*s.meanLog+E/b)*(b:ℝ) := by
    rw [add_mul,div_mul_cancel₀ _ hbp.ne']
    nlinarith only [hc,hH,hC]
  exact hgoal


end QuadraticMoat
