import data.list.sort tactic
import data.nat.log
import init.data.nat

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting

-- USED LEMMAS
lemma log_monotonic : ∀ {a b : ℕ} , a ≤ b → nat.log 2 a ≤ nat.log 2 b
| 0       := begin intros b _, rw nat.log, exact bot_le, end
| (a + 1) := have (a + 1) / 2 < a + 1, from nat.div_lt_self' a 0,
begin
  intros b h,
  cases b,
  { finish, },

  have half_leq : (a + 1) / 2 ≤ (b + 1) / 2 := nat.div_le_div_right h,

  rw nat.log,
  split_ifs,
  { refine ge.le _, rw nat.log, split_ifs,
    { refine add_le_add (log_monotonic half_leq) _, exact rfl.ge, },
    {
      have b_small := not_and_distrib.mp h_2,
      simp only [le_refl, not_le, not_true, or_false, nat.one_lt_bit0_iff]
           at b_small,

      cases b_small with b_small b_small,
      {
        have a_leq_zero := nat.succ_le_succ_iff.mp h,
        have a_is_zero  := eq_bot_iff.mpr a_leq_zero,
        rw a_is_zero at h_1,
        cases h_1 with absurd _,
        by_contradiction,
        exact not_and.mp h_2 absurd b_small,
      },
      by_contra,
      have succ_b_leq_zero := nat.succ_le_succ_iff.mp b_small,
      exact nat.not_succ_le_zero b succ_b_leq_zero,
    },
  },
  exact bot_le,
end

lemma log_pred : ∀ (a : ℕ) , nat.log 2 a - 1 = nat.log 2 (a / 2)
| 0 := by simp
| 1 := by norm_num
| (a + 2) :=
begin
  rw nat.log,
  split_ifs,
  { simp, },
  simp only [le_refl, not_true, zero_le, nat.one_lt_bit0_iff, and_self, le_add_iff_nonneg_left]
       at h,
  cases h,
end

lemma log_2_val : nat.log 2 2 = 1 :=
begin
  rw nat.log,
  split_ifs,
  { simp, },
  simp only [le_refl, not_true, nat.one_lt_bit0_iff, and_self]
       at h,
  cases h,
end

lemma sum_2b (a b : ℕ) : a ≤ 2 * b → a + 2 * b ≤ 4 * b :=
begin
  intro h,
  calc a + 2 * b ≤ 2 * b + 2 * b : by { refine add_le_add h _, exact rfl.ge }
       ...       = 4 * b : by linarith
end

lemma log_2_times : ∀ (a : ℕ), 2 * nat.log 2 (a + 2) ≤ a + 2
| 0       := by { rw log_2_val, norm_num, }
| (a + 1) := have (a + 1) / 2 < a + 1, from nat.div_lt_self' a 0,
begin
  rw nat.log,
  split_ifs,
  { have IH := log_2_times ((a + 1) / 2),
    rw mul_add,
    cases a,
    { norm_num, },
    cases a,
    { norm_num, rw log_2_val, simp, },
    norm_num,
    have add_one : 2 * nat.log 2 ((a.succ.succ + 1) / 2).succ ≤
                   2 * nat.log 2 ((a.succ.succ + 1) / 2 + 2), from
                      by {
                        refine mul_le_mul le_rfl _ bot_le bot_le,
                        refine log_monotonic _,
                        exact nat.le_succ ((a.succ.succ + 1) / 2 + 1),
                      },
    refine le_trans add_one _,
    refine le_trans IH _,
    have succ_succ_two : a.succ.succ + 1 = a + 3 := rfl,
    have two_div_two: ∀ {y}, (y + 2) / 2 = y / 2 + 1 :=
      by { intro, exact (y + 2).div_def 2, },
    have three_eq_one_plus_two : ∀ {y}, y + 3 = y + 1 + 2 :=
      by { intro, exact rfl, },
    rw [ succ_succ_two
       , two_div_two
       , three_eq_one_plus_two
       , ← three_eq_one_plus_two
       ],
    refine add_le_add _ (le_refl 3),
    exact nat.lt_succ_iff.mp (nat.div_lt_self' a 0),
  },
  exact bot_le,
end

lemma div_two : ∀ (b a : ℕ), 2 * a ≤ b → a ≤ b / 2
| 0       a       h := by { norm_num at h, simp only [nat.zero_div, nonpos_iff_eq_zero], exact h, }
| 1       0       h := by norm_num
| 1       (a + 1) h := by { rw mul_add at h, norm_num at h, linarith, }
| (b + 2) 0       h := bot_le
| (b + 2) (a + 1) h :=
begin
  have IH : a ≤ b / 2 := begin
                          refine div_two b a _,
                          rw mul_add at h,
                          simp only [mul_one, add_le_add_iff_right] at h,
                          exact h,
                        end,
  simp only [nat.succ_pos', nat.add_div_right],
  exact nat.succ_le_succ IH,
end

-- SPLIT DEFINITIONS

@[simp] def split : list α → (list α × list α × ℕ)
| []       := ([], [], 0)
| (h :: t) := let (l₁, l₂, n) := split t in (h :: l₂, l₁, n + 1)

theorem split_equivalence : ∀ (l : list α) ,
  (split l).fst = (list.split l).fst ∧ (split l).snd.fst = (list.split l).snd
| [] := by simp
| (h :: t) :=
begin
  simp only [list.split, split],

  have ih := split_equivalence t,
  cases ih with ih_fst ih_snd,

  cases (split t) with t_left₁ t_right₁,
  cases t_right₁ with t_right₁ _,
  unfold split,

  cases t.split with t_left₂ t_right₂,
  unfold list.split,
  simp only [true_and, eq_self_iff_true],

  exact ⟨ ih_snd, ih_fst ⟩,
end

theorem split_complexity : ∀ (l : list α) , (split l).snd.snd = l.length
| [] := by simp
| (h :: t) :=
begin
  simp only [list.length, split],
  have IH := split_complexity t,
  cases split t with l₁ l₂n,
  cases l₂n with l₂ n,
  unfold split,
  rw add_left_inj,
  exact IH,
end

theorem length_split_lt {a b: α} {l l₁ l₂ : list α} {n : ℕ}
  (h : split (a::b::l) = (l₁, l₂, n)):
    list.length l₁ < list.length (a::b::l) ∧
    list.length l₂ < list.length (a::b::l) :=
begin
  have split_eq_full : l₁ = (a::b::l).split.fst ∧ l₂ = (a::b::l).split.snd :=
  begin
    have l₂_n_id : (l₂, n) = (split (a :: b :: l)).snd :=
      (congr_arg prod.snd h).congr_right.mpr rfl,

    have l₂_id : l₂ = (split (a :: b :: l)).snd.fst :=
      (congr_arg prod.fst l₂_n_id).congr_right.mp rfl,

    have l₁_id : l₁ = (split (a :: b :: l)).fst :=
      (congr_arg prod.fst h).congr_right.mpr rfl,

    have split_eq := split_equivalence (a :: b :: l),
    cases split_eq,

    rw split_eq_left at l₁_id,
    rw split_eq_right at l₂_id,

    exact ⟨ l₁_id , l₂_id ⟩,
  end,
  cases split_eq_full,
  have reconstruct : (a::b::l).split = (l₁, l₂) :=
  begin
    rw split_eq_full_left,
    rw split_eq_full_right,
    exact prod.ext rfl rfl,
  end ,
  exact list.length_split_lt reconstruct,
end

theorem split_halves_length : ∀ {l l₁ l₂ : list α} {n : ℕ},
  split l = (l₁, l₂, n) → 
    2 * list.length l₁ ≤ list.length l + 1 ∧ 2 * list.length l₂ ≤ list.length l
| []       :=
begin
  intros l₁ l₂ n h,
  unfold split at h,
  simp only [prod.mk.inj_iff] at h,
  cases h  with h₁ h₂,
  cases h₂ with h₂ _,
  rw [← h₁, ← h₂],
  simp,
end
| (h :: t) :=
begin
  intros l₁ l₂ n h',
  cases e : split t with t₁ t₂m,
  cases t₂m with t₂ m,

  have split_id : split (h :: t) = (h :: t₂, t₁, m + 1) :=
  begin
    rw split,
    cases split t with t₁' t₂',
    cases t₂' with t₂' m₂,
    unfold split,
    injection e,
    injection h_2,
    refine congr (congr_arg prod.mk (congr_arg (list.cons h) h_3)) _,
    rw h_1,
    rw h_4,
  end,
  rw split_id at h',
  injection h',
  injection h_2,

  have IH := split_halves_length e,
  refine and.intro _ _,
  { rw ← h_1, simp only [list.length], linarith, },
  { rw ← h_3, simp only [list.length], linarith, },
end

include r

theorem split_lengths : ∀ (l l₁ l₂ : list α) {n : ℕ},
  split l = (l₁, l₂, n) → l₁.length + l₂.length = l.length
| []  := by { intros l₁ l₂ n,
              simp only [and_imp, prod.mk.inj_iff, list.length, add_eq_zero_iff, split],
              intros h₁ h₂ _,
              rw [← h₁, ← h₂],
              simp,
            }
| [a] := by { intros l₁ l₂ n,
              simp only [and_imp, prod.mk.inj_iff, list.length_singleton, zero_add, split],
              intros h₁ h₂ _,
              rw [← h₁, ← h₂],
              simp,
            }
| (a :: b :: t) :=
begin
  intros l₁ l₂ n h,
  cases e : split t with l₁' l₂'m,
  cases l₂'m with l₂' m,
  simp only [split] at h,
  rw e at h,
  unfold split at h,
  have ih := split_lengths t l₁' l₂' e,
  injection h,
  injection h_2,
  rw [← h_1, ← h_3],
  simp only [list.length], linarith,
end

-- MERGE DEFINITIONS

def merge : list α → list α → (list α × ℕ)
| []       l'        := (l', 0)
| l        []        := (l,  0)
| (a :: l) (b :: l') := if a ≼ b
                        then let (l'', n) :=
                                   merge l (b :: l') in (a :: l'', n + 1)
                        else let (l'', n) :=
                                   merge (a :: l) l' in (b :: l'', n + 1)

theorem merge_complexity : ∀ l l' : list α,
  (merge r l l').snd ≤ l.length + l'.length
| []   []               := by { unfold merge, simp }
| []   (h' :: t')       := by { unfold merge, simp }
| (h :: t)    []        := by { unfold merge, simp }
| (h₁ :: t₁) (h₂ :: t₂) :=
begin
  unfold merge, split_ifs,
  { have IH := merge_complexity t₁ (h₂ :: t₂),
    cases (merge r t₁ (h₂ :: t₂)),
    unfold merge,
    simp only [list.length] at IH,
    simp only [list.length],
    linarith,
  },
  { have IH := merge_complexity (h₁ :: t₁) t₂,
    cases (merge r (h₁ :: t₁) t₂),
    unfold merge,
    simp only [list.length] at IH,
    simp only [list.length],
    linarith,
  }
end

theorem merge_equivalence : ∀ l l' : list α,
  (merge r l l').fst = list.merge r l l'
| []       []         := by { unfold merge, unfold list.merge }
| []       (h' :: t') := by { unfold merge, unfold list.merge }
| (h :: t) []         := by { unfold merge, unfold list.merge }
| (h :: t) (h' :: t') :=
begin
  unfold merge,
  split_ifs,
  { have ih := merge_equivalence t (h' :: t'),
    cases (merge r t (h' :: t')),
    unfold merge,

    unfold list.merge,
    split_ifs,
    exact ⟨ rfl, ih ⟩,
  },
  { have ih := merge_equivalence (h :: t) t',
    cases (merge r (h :: t) t'),
    unfold merge,

    unfold list.merge,
    split_ifs,
    exact ⟨ rfl, ih ⟩,
  }
end

-- MERGE SORT DEFINITIONS

def merge_sort : list α → (list α × ℕ)
| []        := ([],  0)
| [a]       := ([a], 0)
| (a::b::l) := begin
  cases e : split (a::b::l) with l₁ l₂n,
  cases l₂n with l₂ n,
  cases length_split_lt e with h₁ h₂,
  have ms₁ := merge_sort l₁,
  have ms₂ := merge_sort l₂,
  have merged := merge r ms₁.fst ms₂.fst,
  have split_ops := (split (a::b::l)).snd.snd,
  exact ( merged.fst , split_ops + ms₁.snd + ms₂.snd + merged.snd),
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf list.length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

theorem merge_sort_cons_cons_fst {a b n} {l l₁ l₂ : list α}
  (h : split (a::b::l) = (l₁, l₂, n)) :
  (merge_sort r (a::b::l)).fst = (merge r (merge_sort r l₁).fst (merge_sort r l₂).fst).fst :=
begin
  suffices : ∀ (L : list α × ℕ) h1, (@@and.rec
    (λ a a (_ : list.length l₁ < list.length l + 1 + 1 ∧
      list.length l₂ < list.length l + 1 + 1), L) h1 h1).fst = L.fst,
    { simp [merge_sort, h], apply this, },
  intros, cases h1, refl,
end

theorem merge_sort_equivalence : ∀ l : list α , (merge_sort r l).fst = list.merge_sort r l
| []       := by { unfold merge_sort, unfold list.merge_sort }
| [a]      := by { unfold merge_sort, unfold list.merge_sort }
| (a₁ :: a₂ :: t) :=
have (split (a₁ :: a₂ :: t)).fst.length < (a₁ :: a₂ :: t).length :=
begin
  cases e : split (a₁ :: a₂ :: t) with l₁ l₂n,
  cases l₂n with l₂ n,
  cases length_split_lt e with h₁ h₂,
  exact h₁,
end,
have (split (a₁ :: a₂ :: t)).snd.fst.length < (a₁ :: a₂ :: t).length :=
begin
  cases e : split (a₁ :: a₂ :: t) with l₁ l₂n,
  cases l₂n with l₂ n,
  cases length_split_lt e with h₁ h₂,
  exact h₂,
end,
begin
  rw list.merge_sort_cons_cons r (prod.ext rfl rfl),
  rw merge_sort_cons_cons_fst r (prod.ext rfl (prod.ext rfl rfl)),
  rw merge_equivalence,
  rw merge_sort_equivalence,
  rw merge_sort_equivalence,
  rw (split_equivalence (a₁ :: a₂ :: t)).left,
  rw (split_equivalence (a₁ :: a₂ :: t)).right,
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

theorem merge_sort_cons_cons_snd {a b n} {l l₁ l₂ : list α}
  (hs : split (a::b::l) = (l₁, l₂, n)) :
  (merge_sort r (a::b::l)).snd =
    (split (a::b::l)).snd.snd +
    (merge_sort r l₁).snd +
    (merge_sort r l₂).snd +
    (merge r (merge_sort r l₁).fst (merge_sort r l₂).fst).snd
  :=
begin
  suffices : ∀ (L : list α × ℕ) h1, (@@and.rec
    (λ a a (_ : list.length l₁ < list.length l + 1 + 1 ∧
      list.length l₂ < list.length l + 1 + 1), L) h1 h1).snd = L.snd,
    { simp [merge_sort, hs], apply this, },
  intros, cases h1, refl,
end


theorem merge_sort_complexity : ∀ l : list α,
  (merge_sort r l).snd ≤ 8 * l.length * nat.log 2 l.length
| []  := by { unfold merge_sort, simp }
| [a] := by { unfold merge_sort, simp }
| (a₁ :: a₂ :: t) :=
let l := (a₁ :: a₂ :: t) in
begin
  rw merge_sort_cons_cons_snd r (prod.ext rfl (prod.ext rfl rfl)),
  rw split_complexity,

  cases hs : split l with l₁ l₂n,
  cases l₂n with l₂ n,

  cases length_split_lt hs with hh₁ hh₂,

  have l₁_length : 2 * l₁.length ≤ l.length + 1 := (split_halves_length hs).1,
  have l₂_length : 2 * l₂.length ≤ l.length     := (split_halves_length hs).2,
  have l₂_length_half : l₂.length ≤ l.length / 2 := div_two l.length l₂.length l₂_length,
  have ih₁ := merge_sort_complexity l₁,
  have ih₂ := merge_sort_complexity l₂,

  cases h₁ : merge_sort r l₁ with l₁s ns,
  cases h₂ : merge_sort r l₂ with l₂s ms,

  have t_len_l_len : t.length + 2 = l.length := rfl,
  have l₁_length_weak : l₁.length ≤ l.length := by linarith,

  have ms_bound : ms ≤ 4 * l.length * (nat.log 2 l.length - 1) :=
  begin
    have ms_id : (merge_sort r l₂).snd = ms := (congr_arg prod.snd h₂).trans rfl,
    rw ← ms_id,
    refine le_trans ih₂ _,
    rw log_pred l.length,
    calc 8 * l₂.length * nat.log 2 l₂.length
                = 4 * (2 * l₂.length) * nat.log 2 l₂.length : by linarith
            ... ≤ 4 * l.length * nat.log 2 l₂.length : begin rw mul_assoc, rw mul_assoc 4 l.length (nat.log 2 l₂.length),
                                                             refine (mul_le_mul_left zero_lt_four).mpr _,
                                                             exact nat.mul_le_mul_right (nat.log 2 l₂.length) l₂_length,
                                                       end
            ... ≤ 4 * l.length * nat.log 2 (l.length / 2) : begin refine nat.mul_le_mul_left (4 * l.length) _, exact log_monotonic l₂_length_half, end
  end,

  have ns_bound : ns ≤ 4 * (l.length + 1) * nat.log 2 l.length :=
  begin
    have ns_id : (merge_sort r l₁).snd = ns := (congr_arg prod.snd h₁).trans rfl,
    rw ← ns_id,
    refine le_trans ih₁ _,
    calc 8 * l₁.length * nat.log 2 l₁.length
                = 4 * (2 * l₁.length) * nat.log 2 l₁.length : by linarith
            ... ≤ 4 * (l.length + 1) * nat.log 2 l₁.length : begin rw mul_assoc, rw mul_assoc 4 (l.length + 1) (nat.log 2 l₁.length),
                                                                   refine (mul_le_mul_left zero_lt_four).mpr _,
                                                                   exact nat.mul_le_mul_right (nat.log 2 l₁.length) l₁_length,
                                                             end
            ... ≤ 4 * (l.length + 1) * nat.log 2 l.length : begin refine nat.mul_le_mul_left (4 * (l.length + 1)) _, exact log_monotonic l₁_length_weak, end
  end,

  have split_length : l₁s.length + l₂s.length = l.length :=
  begin
    have l₁s_id : (merge_sort r l₁).fst = l₁s := (congr_arg prod.fst h₁).trans rfl,
    rw merge_sort_equivalence at l₁s_id,
    have same_lengths₁ := list.length_merge_sort r l₁,
    have l₁s_len_l₁_len : l₁s.length = l₁.length :=
    begin
      rw l₁s_id at same_lengths₁,
      exact same_lengths₁,
    end,

    have l₂s_id : (merge_sort r l₂).fst = l₂s := (congr_arg prod.fst h₂).trans rfl,
    rw merge_sort_equivalence at l₂s_id,
    have same_lengths₂ := list.length_merge_sort r l₂,
    have l₂s_len_l₂_len : l₂s.length = l₂.length :=
    begin
      rw l₂s_id at same_lengths₂,
      exact same_lengths₂,
    end,
    rw l₁s_len_l₁_len,
    rw l₂s_len_l₂_len,

    exact split_lengths r l l₁ l₂ hs,
  end,

  simp only [list.length],
  rw t_len_l_len,

  have log_l_length : 1 ≤ nat.log 2 l.length :=
  begin
    calc 1 = nat.log 2 2 : log_2_val.symm
         ... ≤ nat.log 2 l.length : by { refine log_monotonic _, linarith, },
  end,

  have four_log_l_length : 4 * 1 * l.length ≤ 4 * nat.log 2 l.length * l.length :=
  begin
    simp only [mul_le_mul_right, nat.succ_pos', mul_one, list.length],
    rw t_len_l_len,
    calc 4 = 4 * 1 : rfl
         ... ≤ 4 * nat.log 2 l.length : by { refine mul_le_mul' _ log_l_length, exact le_refl 4, }
  end,

  calc l.length + ns + ms + (merge r l₁s l₂s).snd
           ≤ l.length + ns + ms + (l₁s.length + l₂s.length) : add_le_add_left (merge_complexity r l₁s l₂s) (l.length + ns + ms)
      ...  = l.length + ns + ms + l.length : congr_arg (has_add.add (list.length l + ns + ms)) split_length
      ...  = 2 * l.length + ns + ms : by ring
      ...  ≤ 2 * l.length + ns + 4 * l.length * (nat.log 2 l.length - 1) : by { refine add_le_add_left _ (2 * l.length + ns), exact ms_bound, }
      ...  ≤ 2 * l.length + 4 * l.length * (nat.log 2 l.length - 1) + ns : by ring_nf
      ...  ≤ 2 * l.length + 4 * l.length * (nat.log 2 l.length - 1) + 4 * (l.length + 1) * nat.log 2 l.length :
        begin
          refine add_le_add_left _ (2 * l.length + 4 * l.length * (nat.log 2 l.length - 1)),
          exact ns_bound,
        end
      ...  ≤ 8 * l.length * nat.log 2 (l.length) :
        begin
          ring_nf,
          rw [ nat.mul_sub_left_distrib
             , add_mul
             , add_mul
             , nat.mul_sub_right_distrib
             ],
          refine (add_le_add_iff_left (4 * 1 * l.length)).mp _,
          rw [ ← add_assoc
             , ← add_assoc
             , ← add_assoc
             , ← nat.add_sub_assoc four_log_l_length (4 * 1 * l.length)
             , add_comm (4 * 1 * l.length) (4 * nat.log 2 l.length * l.length) 
             , nat.add_sub_assoc rfl.ge (4 * nat.log 2 l.length * l.length)
             , nat.sub_self (4 * 1 * l.length)
             ],

          simp only [add_zero, mul_one, list.length],
          rw t_len_l_len,
          ring_nf,

          rw [ add_mul
             , mul_assoc
             , mul_comm l.length (nat.log 2 l.length)
             , ← mul_assoc
             , add_assoc
             ],

          refine (add_le_add_iff_left (8 * nat.log 2 l.length * l.length)).mpr _,
          refine sum_2b (4 * nat.log 2 l.length) l.length _,

          rw ← t_len_l_len,
          have four_two_two: 4 = 2 * 2 := rfl,
          rw four_two_two,
          rw mul_assoc,
          refine mul_le_mul' (le_refl 2) _,
          
          exact log_2_times t.length,
        end,
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

end counting
