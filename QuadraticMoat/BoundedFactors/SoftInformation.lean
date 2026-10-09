import QuadraticMoat.BoundedFactors.SoftLists

namespace OAI.GaussianMoat.FinLaw
open scoped BigOperators Classical
universe uι uO uΓ uG uΩ

lemma joint_soft_entropy {ι : Type uι} {O : Type uO} {Γ : Type uΓ}
    [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uG) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ) {h : ℝ} (hh : 0 < h) :
    (p.joint (fun a => (q a).iid n)).cHf (fun v => v.1.2)
      (fun v => (v.1.1,v.2)) ≤
      (Fintype.card ι:ℝ)*Real.log 2 +
      (∑ a, p a*(∑ i, ∑ v, (q a).iid n v*logMaxCard (softList (hit i) n h v))) +
      (n:ℝ)/h * ∑ i, Real.log (Fintype.card (G i)) *
        (p.joint q).prob (fun v => hit i v.2 (v.1.2 i)) := by
  let P := p.joint (fun a => (q a).iid n)
  let C := fun v : (O × (∀ i, G i)) × (Fin n → Γ) => (v.1.1,v.2)
  letI : Nonempty (O × (∀ i, G i)) := p.nonempty
  letI (i : ι) : Nonempty (G i) := ⟨(Classical.arbitrary (O × (∀ i, G i))).2 i⟩
  have hcoordinate (i : ι) :
      P.cHf (fun v => v.1.2 i) C ≤ Real.log 2 +
      (∑ a, p a * ∑ v, (q a).iid n v * logMaxCard (softList (hit i) n h v)) +
      (n:ℝ)/h * Real.log (Fintype.card (G i)) *
        (p.joint q).prob (fun v => hit i v.2 (v.1.2 i)) := by
    have hl := P.variable_short_list (fun v => v.1.2 i) C
      (fun c => softList (hit i) n h c.2)
    have he : (∑ v, P v * logMaxCard (softList (hit i) n h v.2)) =
        ∑ a, p a * ∑ v, (q a).iid n v * logMaxCard (softList (hit i) n h v) := by
      simp only [P, Fintype.sum_prod_type, joint_mass, Finset.mul_sum, mul_assoc]
    change P.cHf (fun v => v.1.2 i) C ≤ Real.log 2 +
      (∑ v, P v * logMaxCard (softList (hit i) n h v.2)) +
      P.prob (fun v => v.1.2 i ∉ softList (hit i) n h v.2) * Real.log (Fintype.card (G i)) at hl
    rw [he] at hl
    have herr : P.prob (fun v => v.1.2 i ∉ softList (hit i) n h v.2) ≤
        (n:ℝ)/h * (p.joint q).prob (fun v => hit i v.2 (v.1.2 i)) := by
      dsimp only [P]
      rw [prob_joint, prob_joint, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      have hm := mul_le_mul_of_nonneg_left ((q a).softList_true_error (hit i) n hh (a.2 i)) (p.nonneg a)
      convert hm using 1 <;> ring
    have hlog : 0 ≤ Real.log (Fintype.card (G i)) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
    have hm := mul_le_mul_of_nonneg_right herr hlog
    nlinarith only [hl, hm]
  have hs := (P.cHf_dpi_subadd G (fun i v => v.1.2 i) C).trans
    (Finset.sum_le_sum (fun i _ => hcoordinate i))
  apply hs.trans
  apply le_of_eq
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  · rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem soft_information_lower {ι : Type uι} {O : Type uO} {Γ : Type uΓ}
    [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uG) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ) {h : ℝ} (hh : 0 < h)
    (Bad : ι → O × (∀ i, G i) → Prop) {A H η : ℝ} (hA : 0 ≤ A)
    (hH : (∑ i, Real.log (Fintype.card (G i)))-H ≤ p.cHf Prod.snd Prod.fst)
    (hBad : (∑ i, p.prob (Bad i)) ≤ η)
    (hlist : ∀ a, p a ≠ 0 → ∀ i,
      (∑ v, (q a).iid n v*logMaxCard (softList (hit i) n h v)) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1)) :
    A*((Fintype.card ι:ℝ)-η)-H-(Fintype.card ι:ℝ)*Real.log 2-
      (n:ℝ)/h*∑ i, Real.log (Fintype.card (G i))*
        (p.joint q).prob (fun v => hit i v.2 (v.1.2 i)) ≤
      (n:ℝ)*(p.joint q).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
  let P := p.joint (fun a => (q a).iid n)
  have hcond := joint_soft_entropy G p q hit n hh
  have hsum : (∑ a, p a*(∑ i, ∑ v, (q a).iid n v*logMaxCard (softList (hit i) n h v))) ≤
      (∑ i, Real.log (Fintype.card (G i)))-A*((Fintype.card ι:ℝ)-∑ i, p.prob (Bad i)) := by
    calc
      _ ≤ ∑ a, p a*(∑ i, (Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1))) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : p a=0
        · simp only [ha, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlist a ha i)) (p.nonneg a)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, mul_sub, ← Finset.sum_mul, p.sum_one, one_mul]
        congr 1
        rw [mul_comm]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        have he (i : ι) : (∑ a, p a*(if Bad i a then (0:ℝ) else 1)) = 1-p.prob (Bad i) := by
          rw [← p.prob_compl]
          unfold prob
          apply Finset.sum_congr rfl
          intro a _
          by_cases hb : Bad i a <;> simp [hb]
        have he' (i : ι) : (∑ a, p a*(A*(if Bad i a then (0:ℝ) else 1))) = A*(1-p.prob (Bad i)) := by
          rw [← he i, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
        simp only [he', mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
  have hinit : P.cHf (fun v => v.1.2) (fun v => v.1.1) = p.cHf Prod.snd Prod.fst := by
    have he := P.cHf_map Prod.fst Prod.snd Prod.fst
    rw [joint_map_fst] at he
    exact he.symm
  have hlow : A*((Fintype.card ι:ℝ)-η)-H-(Fintype.card ι:ℝ)*Real.log 2-
      (n:ℝ)/h*∑ i, Real.log (Fintype.card (G i))*
        (p.joint q).prob (fun v => hit i v.2 (v.1.2 i)) ≤
      P.cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
    unfold cIf
    rw [hinit]
    have hm := mul_le_mul_of_nonneg_left hBad hA
    change P.cHf (fun v => v.1.2) (fun v => (v.1.1,v.2)) ≤ _ at hcond
    linarith only [hH, hcond, hsum, hm]
  exact hlow.trans (conditional_iid_information p q n)

theorem posterior_soft_information_lower {Ω : Type uΩ} {ι : Type uι} {O : Type uO} {Γ : Type uΓ}
    [Fintype Ω] [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uG) [∀ i, Fintype (G i)]
    (p : FinLaw Ω) (old : Ω → O) (X : Ω → ∀ i, G i) (q : Ω → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (Good : ι → Ω → Prop)
    (E : (i : ι) → Ω → Finset (G i)) (e c : ι → ℝ) {A H η h : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (hh : 0 < h) (he : ∀ i, 0 ≤ e i) (hc : ∀ i, 0 < c i)
    (hthreshold : ∀ i, h ≤ (n:ℝ)*c i/8)
    (hE : ∀ i ω, Good i ω → ((E i ω).card:ℝ) ≤ e i)
    (hhit : ∀ i ω, Good i ω → ∀ x ∉ E i ω, c i ≤ (q ω).prob (fun v => hit i v x))
    (hH : (∑ i, Real.log (Fintype.card (G i)))-H ≤ p.cHf X old)
    (hBad : (∑ i, p.prob (fun ω => ¬Good i ω)) ≤ η)
    (hnum : ∀ i, Real.log (1+4*e i+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*c i/32)) ≤
      Real.log (Fintype.card (G i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H-(Fintype.card ι:ℝ)*Real.log 2-
      (n:ℝ)/h*∑ i, Real.log (Fintype.card (G i))*
        (p.joint q).prob (fun v => hit i v.2 (X v.1 i)) ≤
      (n:ℝ)*(p.joint q).cIf (fun v => X v.1) Prod.snd (fun v => old v.1) := by
  let C := fun ω => (old ω,X ω)
  let μ := p.map C
  let Q := fun a => (p.conditionOn C a).mix q
  let Bad := fun i a => (1/2:ℝ) < (p.conditionOn C a).prob (fun ω => ¬Good i ω)
  letI : Nonempty Ω := p.nonempty
  letI (i : ι) : Nonempty (G i) := ⟨X (Classical.arbitrary Ω) i⟩
  have hH' : (∑ i, Real.log (Fintype.card (G i)))-H ≤ μ.cHf Prod.snd Prod.fst := by
    rw [cHf_map]
    exact hH
  have hBad' : (∑ i, μ.prob (Bad i)) ≤ 2*η := by
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      p.posterior_unfavorable C (fun ω => ¬Good i ω))
    simp only [← Finset.mul_sum] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hBad (by norm_num))
  have hlist (a : O × (∀ i, G i)) (ha : μ a ≠ 0) (i : ι) :
      (∑ v, (Q a).iid n v*logMaxCard (softList (hit i) n h v)) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1) := by
    by_cases hb : Bad i a
    · rw [ite_eq_left hb, mul_zero, sub_zero]
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
        mul_le_mul_of_nonneg_left (logMaxCard_le_card (softList (hit i) n h v)) (((Q a).iid n).nonneg v))
      simpa only [← Finset.sum_mul, ((Q a).iid n).sum_one, one_mul] using hs
    · rw [ite_eq_right hb, mul_one]
      have hg : (1/2:ℝ) ≤ (p.conditionOn C a).prob (Good i) := by
        have hh := (p.conditionOn C a).prob_compl (Good i)
        dsimp only [Bad] at hb
        push Not at hb
        linarith only [hh, hb]
      let F := Finset.univ.filter (fun x : G i =>
        (p.conditionOn C a).prob (fun ω => Good i ω ∧ x ∉ E i ω) < 1/4)
      have hf : (F.card:ℝ) ≤ 4*e i :=
        (p.conditionOn C a).mixed_exception_card (Good i) (E i) (he i) (hE i) hg
      have hm (x : G i) (hx : x ∉ F) : c i/4 ≤ (Q a).prob (fun v => hit i v x) := by
        apply (p.conditionOn C a).mixed_floor q (Good i) (E i) (hit i) (hc i).le (hhit i) x
        have he : ¬(p.conditionOn C a).prob (fun ω => Good i ω ∧ x ∉ E i ω) < 1/4 := by
          simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and] using hx
        exact le_of_not_gt he
      have ht := (Q a).expected_logMaxCard_softList (hit i) F n (hc i) (hthreshold i) hm
      have hl := Real.log_le_log
        (by positivity : (0:ℝ) < 1+(F.card:ℝ)+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*c i/32))
        (by linarith : 1+(F.card:ℝ)+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*c i/32) ≤
          1+4*e i+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*c i/32))
      exact ht.trans (hl.trans (hnum i))
  have ht := soft_information_lower G μ Q hit n hh Bad hA hH' hBad' hlist
  have hdist : μ.joint Q = (p.joint q).map (fun v => (C v.1,v.2)) :=
    p.joint_conditionOn_mix C q
  rw [hdist, cIf_map] at ht
  simp only [prob_map] at ht
  exact ht

end OAI.GaussianMoat.FinLaw
