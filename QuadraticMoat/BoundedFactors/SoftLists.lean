import OAI.NumberTheory.GaussianMoat.PassingInformation

namespace OAI.GaussianMoat.FinLaw
open scoped BigOperators Classical
universe uΩ uΓ uG uα
variable {Ω : Type uΩ} {Γ : Type uΓ} {G : Type uG} {α : Type uα}
variable [Fintype Ω] [Fintype Γ] [Fintype G] [Fintype α]

noncomputable def hitCount (hit : Γ → G → Prop) (n : ℕ) (v : Fin n → Γ) (x : G) : ℝ :=
  ∑ j, if hit (v j) x then 1 else 0

noncomputable def softList (hit : Γ → G → Prop) (n : ℕ) (h : ℝ) (v : Fin n → Γ) : Finset G :=
  Finset.univ.filter (fun x => hitCount hit n v x ≤ h)

noncomputable def logMaxCard (L : Finset G) : ℝ := Real.log (max 1 (L.card : ℝ))

lemma logMaxCard_nonneg (L : Finset G) : 0 ≤ logMaxCard L :=
  Real.log_nonneg (le_max_left _ _)

lemma logMaxCard_le_card (L : Finset G) [Nonempty G] :
    logMaxCard L ≤ Real.log (Fintype.card G) := by
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply max_le
  · exact_mod_cast Fintype.card_pos
  · exact_mod_cast Finset.card_le_univ L

lemma softList_candidate_tail (p : FinLaw Γ) (hit : Γ → G → Prop)
    (n : ℕ) {h c : ℝ} (hc : 0 < c) (hh : h ≤ (n:ℝ)*c/8)
    (x : G) (hp : c/4 ≤ p.prob (fun v => hit v x)) :
    (p.iid n).prob (fun v => x ∈ softList hit n h v) ≤ Real.exp (-(n:ℝ)*c/32) := by
  have ht := p.iid_lower_tail (fun v => hit v x) n
    (μ := c/4) (δ := c/8) (by positivity) (by positivity) hp
  have hm := (p.iid n).prob_mono (E := fun v => x ∈ softList hit n h v)
    (F := fun v => (∑ j : Fin n, if hit (v j) x then (1:ℝ) else 0) ≤ (n:ℝ)*(c/4-c/8))
    (fun v hv => by
      have hv' : hitCount hit n v x ≤ h := by simpa [softList] using hv
      dsimp [hitCount] at hv'
      nlinarith)
  apply hm.trans
  convert ht using 1
  congr 1
  field_simp
  <;> ring

lemma expect_card_softList (p : FinLaw Γ) (hit : Γ → G → Prop) (E : Finset G)
    (n : ℕ) {h c : ℝ} (hc : 0 < c) (hh : h ≤ (n:ℝ)*c/8)
    (hp : ∀ x ∉ E, c/4 ≤ p.prob (fun v => hit v x)) :
    (∑ v, p.iid n v * ((softList hit n h v).card:ℝ)) ≤
      (E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c/32) := by
  have he : (∑ v, p.iid n v * ((softList hit n h v).card:ℝ)) =
      ∑ x : G, (p.iid n).prob (fun v => x ∈ softList hit n h v) := by
    have hcard (v : Fin n → Γ) : ((softList hit n h v).card:ℝ) =
        ∑ x : G, if x ∈ softList hit n h v then (1:ℝ) else 0 := by simp
    simp only [hcard, Finset.mul_sum, prob]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  rw [he]
  have hb (x : G) : (p.iid n).prob (fun v => x ∈ softList hit n h v) ≤
      (if x ∈ E then (1:ℝ) else 0)+Real.exp (-(n:ℝ)*c/32) := by
    by_cases hx : x ∈ E
    · simp only [hx, ite_true]
      exact ((p.iid n).prob_le_one _).trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    · simp only [hx, ite_false, zero_add]
      exact softList_candidate_tail p hit n hc hh x (hp x hx)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hb x)
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hs

lemma expected_logMaxCard_softList (p : FinLaw Γ) (hit : Γ → G → Prop) (E : Finset G)
    (n : ℕ) {h c : ℝ} (hc : 0 < c) (hh : h ≤ (n:ℝ)*c/8)
    (hp : ∀ x ∉ E, c/4 ≤ p.prob (fun v => hit v x)) :
    (∑ v, p.iid n v * logMaxCard (softList hit n h v)) ≤
      Real.log (1+(E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c/32)) := by
  have hj := (p.iid n).expect_log_le_log_expect
    (fun v => max 1 ((softList hit n h v).card:ℝ))
    (fun _ _ => lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply hj.trans
  have hlo : 1 ≤ ∑ v, p.iid n v * max 1 ((softList hit n h v).card:ℝ) := by
    calc
      1 = ∑ v, p.iid n v * 1 := by simp only [mul_one, (p.iid n).sum_one]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (le_max_left _ _) ((p.iid n).nonneg v))
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one hlo)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
    mul_le_mul_of_nonneg_left (max_le (by have hc := Nat.cast_nonneg (softList hit n h v).card (α := ℝ); linarith : (1:ℝ) ≤ 1+((softList hit n h v).card:ℝ))
      (by linarith : ((softList hit n h v).card:ℝ) ≤ 1+((softList hit n h v).card:ℝ))) ((p.iid n).nonneg v))
  have hb := expect_card_softList p hit E n hc hh hp
  simp only [mul_add, mul_one, Finset.sum_add_distrib, (p.iid n).sum_one] at hs
  linarith

/-- A random list may be empty; a failed membership test costs the full alphabet entropy. -/
lemma variable_short_list (p : FinLaw Ω) (X : Ω → G) (Y : Ω → α) (L : α → Finset G) :
    p.cHf X Y ≤ Real.log 2 + (∑ ω, p ω * logMaxCard (L (Y ω))) +
      p.prob (fun ω => X ω ∉ L (Y ω)) * Real.log (Fintype.card G) := by
  let E : Ω → Bool := fun ω => decide (X ω ∈ L (Y ω))
  let L' : α × Bool → Finset G := fun ye => if ye.2 = true then L ye.1 else Finset.univ
  have hs : ∀ ω, p ω ≠ 0 → X ω ∈ L' (Y ω,E ω) := by
    intro ω _
    by_cases hm : X ω ∈ L (Y ω) <;> simp [L', E, hm]
  have hc := p.condH_le_support X (fun ω => (Y ω,E ω)) L' hs
  have hcard (ye : α × Bool) : Real.log (L' ye).card ≤
      logMaxCard (L ye.1) + (if ye.2 = true then 0 else Real.log (Fintype.card G)) := by
    by_cases he : ye.2 = true
    · simp only [L', he, ite_true, add_zero]
      exact log_card_le_real _ (le_max_left _ _) (le_max_right _ _)
    · simp only [L', he, ite_false, Finset.card_univ]
      exact le_add_of_nonneg_left (logMaxCard_nonneg _)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ye _ =>
    mul_le_mul_of_nonneg_left (hcard ye) ((p.map (fun ω => (Y ω,E ω))).nonneg ye))
  simp only [expect_map] at hc hh
  have he : (∑ ω, p ω * (logMaxCard (L (Y ω)) +
      (if E ω = true then 0 else Real.log (Fintype.card G)))) =
      (∑ ω, p ω * logMaxCard (L (Y ω))) +
      p.prob (fun ω => X ω ∉ L (Y ω)) * Real.log (Fintype.card G) := by
    simp only [mul_add, Finset.sum_add_distrib, prob, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hm : X ω ∈ L (Y ω) <;> simp [E, hm]
  rw [he] at hh
  have hr := p.condH_le_reveal X Y E
  have hE : p.H E ≤ Real.log 2 := by
    simpa only [Hf_eq_H, Fintype.card_bool, Nat.cast_ofNat] using p.Hf_le_log_card_type E
  have hfinal : p.condH X Y ≤ Real.log 2 + (∑ ω, p ω * logMaxCard (L (Y ω))) +
      p.prob (fun ω => X ω ∉ L (Y ω)) * Real.log (Fintype.card G) := by linarith
  simpa only [condH, ← Hf_eq_H, cHf] using hfinal

lemma expect_hitCount_iid (p : FinLaw Γ) (hit : Γ → G → Prop) (n : ℕ) (x : G) :
    (∑ v, p.iid n v * hitCount hit n v x) = (n:ℝ)*p.prob (fun v => hit v x) := by
  simp only [hitCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (j : Fin n) : (∑ v, p.iid n v * (if hit (v j) x then (1:ℝ) else 0)) =
      p.prob (fun v => hit v x) := by
    rw [← expect_map (p.iid n) (fun v => v j) (fun v => if hit v x then (1:ℝ) else 0), iid_map_eval]
    unfold prob
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma softList_true_error (p : FinLaw Γ) (hit : Γ → G → Prop) (n : ℕ) {h : ℝ}
    (hh : 0 < h) (x : G) :
    (p.iid n).prob (fun v => x ∉ softList hit n h v) ≤
      (n:ℝ)/h*p.prob (fun v => hit v x) := by
  have hm := (p.iid n).prob_le_expect_div (fun v => hitCount hit n v x)
    (fun v => Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)) hh
  rw [expect_hitCount_iid] at hm
  convert hm using 1
  · congr 1
    funext v
    simp [softList, not_le]
  · ring

end OAI.GaussianMoat.FinLaw
