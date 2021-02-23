import data.list.sort tactic
import data.nat.log

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting

theorem easy_le {a b : ℕ} : 2 * a ≤ 2 * b → a ≤ b := by { intro h, omega }
theorem easy_eq {a b : ℕ} : 2 * a = 2 * b → a = b := by { intro h, omega }

@[simp] def split : list α → (list α × list α × ℕ)
| []       := ([], [], 0)
| (h :: t) := let (l₁, l₂, n) := split t in (h :: l₂, l₁, n + 1)

theorem split_equivalence : ∀ (l : list α) ,
  (split l).fst = (list.split l).fst ∧ (split l).snd.fst = (list.split l).snd
| [] := by simp
| (h :: t) :=
begin
  simp,

  have ih := split_equivalence t,
  cases ih with ih_fst ih_snd,

  cases (split t) with t_left₁ t_right₁,
  cases t_right₁ with t_right₁ _,
  unfold split,

  cases t.split with t_left₂ t_right₂,
  unfold list.split,
  simp,

  exact ⟨ ih_snd, ih_fst ⟩,
end

theorem split_complexity : ∀ (l : list α) , (split l).snd.snd = l.length
| [] := by simp
| (h :: t) :=
begin
  simp,
  have ih := split_complexity t,
  cases split t with l₁ l₂n,
  cases l₂n with l₂ n,
  unfold split,
  simp,
  exact ih,
end

theorem length_split_lt {a b} {l l₁ l₂ : list α} {n : ℕ} (h : split (a::b::l) = (l₁, l₂, n)) :
  list.length l₁ < list.length (a::b::l) ∧ list.length l₂ < list.length (a::b::l) :=
begin
  have eq_mathlib : l₁ = (a::b::l).split.fst ∧ l₂ = (a::b::l).split.snd :=
  begin
    have l₂_n_id : (l₂, n) = (split (a :: b :: l)).snd := (congr_arg prod.snd h).congr_right.mpr rfl,
    have l₂_id : l₂ = (split (a :: b :: l)).snd.fst := (congr_arg prod.fst l₂_n_id).congr_right.mp rfl,
    have l₁_id : l₁ = (split (a :: b :: l)).fst := (congr_arg prod.fst h).congr_right.mpr rfl,
    have split_eq := split_equivalence  (a :: b :: l),
    cases split_eq,

    rw split_eq_left at l₁_id,
    rw split_eq_right at l₂_id,

    exact ⟨ l₁_id , l₂_id ⟩,
  end,
  cases eq_mathlib,
  have reconstruct : (a::b::l).split = (l₁, l₂) :=
  begin
    rw eq_mathlib_left,
    rw eq_mathlib_right,
    exact prod.ext rfl rfl,
  end ,
  exact list.length_split_lt reconstruct,
end

theorem split_halves_length : ∀ {l l₁ l₂ : list α} {n : ℕ} , split l = (l₁, l₂, n) → 
  2 * list.length l₁ ≤ list.length l + 1 ∧ 2 * list.length l₂ ≤ list.length l
| [] := begin intros l₁ l₂ n h, unfold split at h, simp at h, cases h with h₁ h₂, cases h₂ with h₂ _, rw ← h₁, rw ← h₂, simp, end
| (h :: t) :=
begin
  intros l₁ l₂ n h',
  cases e : split t with t₁ t₂m,
  cases t₂m with t₂ m,

  have split_id : split (h :: t) = (h :: t₂, t₁, m + 1) :=
  begin
    simp,
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

  have ih := split_halves_length e,
  refine and.intro _ _,
  { rw ← h_1, simp, linarith, },
  { rw ← h_3, simp, linarith, },
end

theorem zero_not_odd : ¬ odd 0 :=
begin
  intro h,
  cases h,
  finish,
end

theorem wot : ∀ n : ℕ , 0 < n →  1 < 2 * n
| 0 := begin intro h', by_contra, exact nat.lt_asymm h' h', end
| (n + 1) := 
begin
  intro h,
  rw mul_add,
  norm_num,
  exact (cmp_eq_lt_iff 1 (2 * n + 2)).mp rfl,
end

theorem one_not_even : ¬ even 1 :=
begin
  intro h,
  cases h,
  cases h_w,
  { simp at h_h,exact h_h, },
  
  have h_w_succ_pos : 0 < h_w.succ := fin.last_pos,
  have h_w_succ_gt_1 : 1 < 2 * h_w.succ := wot h_w.succ h_w_succ_pos,
  rw ← h_h at h_w_succ_gt_1,
  exact nat.lt_asymm h_w_succ_gt_1 h_w_succ_gt_1,
end

theorem div_two : ∀ (b a : ℕ) , 2 * a = b → a = b / 2 
| 0       a       := begin intro h, simp, exact easy_eq h, end
| 1       a       := begin intro h, have q : even 1 := begin use a, exact h.symm end, by_contra, exact one_not_even q, end
| (b + 2) 0       := begin intro h, finish, end
| (b + 2) (a + 1) :=
begin
  intros h,
  have q : a = b / 2 := begin refine div_two b a _, rw mul_add at h, simp at h, exact h, end,
  rw q,
  ring,
end

def merge : list α → list α → (list α × ℕ)
| []       l'        := (l', 0)
| l        []        := (l,  0)
| (a :: l) (b :: l') := if a ≼ b
                        then let (l'', n) := merge l (b :: l') in (a :: l'', n + 1)
                        else let (l'', n) := merge (a :: l) l' in (b :: l'', n + 1)

include r

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

theorem merge_complexity : ∀ l l' : list α , (merge r l l').snd ≤ l.length + l'.length
| []   []               := by { unfold merge, simp }
| []   (h' :: t')       := by { unfold merge, simp }
| (h :: t)    []        := by { unfold merge, simp }
| (h₁ :: t₁) (h₂ :: t₂) :=
begin
  unfold merge, split_ifs,
  { have hh := merge_complexity t₁ (h₂ :: t₂),
    cases (merge r t₁ (h₂ :: t₂)),
    unfold merge,
    simp at hh,
    simp,
    linarith,
  },
  { have hh := merge_complexity (h₁ :: t₁) t₂,
    cases (merge r (h₁ :: t₁) t₂),
    unfold merge,
    simp at hh,
    simp,
    linarith,
  }
end

theorem merge_equivalence : ∀ l l' : list α , (merge r l l').fst = list.merge r l l'
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

theorem log_monotonic : ∀ {a b : ℕ} , a ≤ b → nat.log 2 a ≤ nat.log 2 b
| 0  := begin intros b h, exact bot_le, end
| (n+1) := have (n + 1) / 2 < n + 1, from nat.div_lt_self' n 0,
begin
  intros b h,
  cases b,
  { finish, },

  have half_leq : (n + 1) / 2 ≤ (b + 1) / 2 := nat.div_le_div_right h,
  have ih := log_monotonic half_leq,
  rw nat.log,
  split_ifs,
  { refine ge.le _, rw nat.log, split_ifs,
    { refine add_le_add (log_monotonic half_leq) _, exact rfl.ge},
    {
      have hh := not_and_distrib.mp h_2,
      simp at hh,
      cases hh,
      {
        have absurd : b.succ < b.succ := calc b.succ < 2      : hh
                                              ...    ≤ n + 1  : h_1.1
                                              ...    ≤ b.succ : h,
        by_contra,
        exact nat.lt_asymm absurd absurd,
      },
      by_contra,
      exact nat.lt_asymm hh hh,
    },
  },
  exact bot_le,
end

theorem split_lengths {l l₁ l₂ : list α} {n : ℕ} : split l = (l₁, l₂, n) → l₁.length + l₂.length = l.length :=
begin
  sorry,
end


theorem log_pred : ∀ (a : ℕ) , nat.log 2 a - 1 = nat.log 2 (a / 2)
| 0 := begin simp, rw nat.log, split_ifs, { finish, }, simp, end 
| 1 := begin rw nat.log, split_ifs, { exact rfl, }, simp, rw nat.log, split_ifs, { have absurd := h_1.1, norm_num at absurd, }, exact rfl, end
| (a + 2) :=
begin
  rw nat.log,
  split_ifs,
  { exact rfl, },
  simp at h,
  have h' := h,
  by_contra,
  exact nat.lt_asymm h' h',
end

theorem minus (c a b : ℕ) : c - (a + b) = c - a - b :=
begin
  omega,
end

theorem log_2_val : nat.log 2 2 = 1 :=
begin
  rw nat.log,
  split_ifs,
  { simp, rw nat.log, split_ifs, { by_contra, have s := h_1.1, exact nat.lt_asymm s s, }, simp, },
  simp at h, omega,
end

theorem sum_2b (a b : ℕ) : a ≤ 2 * b → a + 2 * b ≤ 4 * b :=
begin
  intro h,
  calc a + 2 * b ≤ 2 * b + 2 * b : by { refine add_le_add h _, exact rfl.ge }
       ...       = 4 * b : by linarith
end

theorem log_2_times : ∀ (a : ℕ) , 1 < a → 4 * nat.log 2 a ≤ 2 * a
| 0 := begin intro h, norm_num at h, end
| 1 := begin intro h, norm_num at h, end
| 2 := begin intro h, rw nat.log, split_ifs, { simp, rw nat.log, split_ifs, { have abs := h_2.1, norm_num at abs, }, norm_num, }, norm_num, end
| 3 := begin intro h, rw nat.log, split_ifs, { rw nat.log, split_ifs, { have abs := h_2.1, norm_num at abs, }, norm_num, }, norm_num, end
| (a + 4) := have (a + 4) / 2 < a + 4 := (a + 3).div_lt_self' 0,
begin
  intro h,
  have hh : 1 < ((a + 4) / 2) := (cmp_eq_lt_iff 1 ((a + 4) / 2)).mp rfl,
  have ih := log_2_times ((a + 4) / 2) hh,
  
  rw ← log_pred (λ {xx yy : ℕ} , xx ≤ yy) (a + 4) at ih,

  rw nat.mul_sub_left_distrib 4 (nat.log 2 (a + 4)) 1 at ih,
  simp at ih,

  have leq_1 : 4 * nat.log 2 (a + 4) ≤ 2 * ((a + 4) / 2) + 4 := nat.le_add_of_sub_le_right ih,
  have leq_2 : 2 * ((a + 4) / 2) + 4 ≤ 2 * (a + 4) :=
  begin
    calc 2 * ((a + 4) / 2) + 4 ≤ a + 4 + 4 : begin rw mul_comm, refine (add_le_add_iff_right 4).mpr _, exact (nat.div_mul_le_self (a + 4) 2), end
         ...                   ≤ a + a + 4 + 4 : nat.le_add_left (a + 4 + 4) a
         ...                   = 2 * (a + 4) : by linarith
  end,
  exact le_trans leq_1 leq_2,
end

theorem merge_sort_complexity : ∀ l : list α , (merge_sort r l).snd ≤ 8 * l.length * nat.log 2 l.length
| []  := by { unfold merge_sort, simp }
| [a] := by { unfold merge_sort, simp }
| (a₁ :: a₂ :: t) := let l := (a₁ :: a₂ :: t) in
begin
  rw merge_sort_cons_cons_snd r (prod.ext rfl (prod.ext rfl rfl)),
  rw split_complexity,

  cases hs : split l with l₁ l₂n,
  cases l₂n with l₂ n,

  have l₁_length : 2 * l₁.length ≤ l.length + 1 := (split_halves_length hs).1,
  have l₂_length : 2 * l₂.length ≤ l.length     := (split_halves_length hs).2,

  have ih₁ := merge_sort_complexity l₁,
  have ih₂ := merge_sort_complexity l₂,

  cases h₁ : merge_sort r l₁ with l₁s ns,
  cases h₂ : merge_sort r l₂ with l₂s ms,

  have t_len_l_len : t.length + 2 = l.length := rfl,

  have l₂_length_weak : l₂.length ≤ l.length := by linarith,
  have l₁_length_weak : l₁.length ≤ l.length := by linarith,
  have one_lt_l_length : 1 < l.length   := by linarith,
  have l_length_pos  : 0 < l.length     := by linarith,
  have l_length_gt_1 : 0 < l.length + 1 := by linarith,

  have ms_bound : ms ≤ 4 * l.length * (nat.log 2 l.length - 1) :=
  begin
    sorry,
    -- rw h₂ at ih₂,
    -- simp at ih₂,
    -- have log_leq := log_monotonic (λ {x y : ℕ} , x ≤ y) l₂_length_weak,
    -- calc 2 * ms ≤ 2 * (l₂.length * nat.log 2 l₂.length) : -- (mul_le_mul_left zero_lt_two).mpr ih₂
    --      ...    = (2 * l₂.length) * nat.log 2 l₂.length : by rw ← mul_assoc 2 l₂.length (nat.log 2 l₂.length)
    --      ...    ≤ l.length * nat.log 2 l₂.length        : by { refine nat.mul_le_mul l₂_length _, exact rfl.ge }
    --      ...    ≤ l.length * nat.log 2 l.length         : (mul_le_mul_left l_length_pos).mpr log_leq,
  end,

  have ns_bound : ns ≤ 4 * (l.length + 1) * nat.log 2 l.length :=
  begin
    sorry,
    -- rw t_len_l_len,
    -- rw h₁ at ih₁,
    -- simp at ih₁,
    -- have log_leq := log_monotonic (λ {x y : ℕ} , x ≤ y) l₁_length_weak,

    -- calc 2 * ns ≤ 2 * (l₁.length * nat.log 2 l₁.length) :  -- (mul_le_mul_left zero_lt_two).mpr ih₁
    --      ...    = (2 * l₁.length) * nat.log 2 l₁.length : by rw ← mul_assoc 2 l₁.length (nat.log 2 l₁.length)
    --      ...    ≤ (l.length + 1) * nat.log 2 l₁.length  : by { refine nat.mul_le_mul l₁_length _, exact rfl.ge }
    --      ...    ≤ (l.length + 1) * nat.log 2 l.length   : (mul_le_mul_left l_length_gt_1).mpr log_leq,

  end,

  have split_length : l₁s.length + l₂s.length = l.length := sorry,

  -- have l₁s_length : l₁s.length ≤ t.length + 1 :=
  -- begin
  --   have l₁s_id : l₁s = (merge_sort r l₁).fst := by rw h₁,
  --   rw l₁s_id,
  --   rw merge_sort_equivalence r l₁,
  --   rw list.length_merge_sort,

  --   cases length_split_lt hs with l₁_length _,

  --   exact nat.lt_succ_iff.mp l₁_length,
  -- end,

  -- have l₂s_length : l₂s.length ≤ t.length + 1 :=
  -- begin
  --   have l₂s_id : l₂s = (merge_sort r l₂).fst := by rw h₂,
  --   rw l₂s_id,
  --   rw merge_sort_equivalence r l₂,
  --   rw list.length_merge_sort,

  --   cases length_split_lt hs with _ l₂_length,

  --   exact nat.lt_succ_iff.mp l₂_length,
  -- end,

  simp,
  rw t_len_l_len,

  have log_l_length : 1 ≤ nat.log 2 l.length :=
  begin
    calc 1 = nat.log 2 2 : (log_2_val (λ {xx yy : ℕ} , xx ≤ yy)).symm
         ... ≤ nat.log 2 l.length : begin  refine log_monotonic (λ {xx yy : ℕ} , xx ≤ yy) _, linarith, end
  end,

  have four_log_l_length : 4 * 1 * l.length ≤ 4 * nat.log 2 l.length * l.length :=
  begin
    simp,
    rw t_len_l_len,
    calc 4 = 4 * 1 : rfl
         ... ≤ 4 * nat.log 2 l.length : sup_eq_left.mp rfl
  end,

  calc l.length + ns + ms + (merge r l₁s l₂s).snd
           ≤ l.length + ns + ms + (l₁s.length + l₂s.length) : add_le_add_left (merge_complexity r l₁s l₂s) (l.length + ns + ms)
      ...  = l.length + ns + ms + l.length : congr_arg (has_add.add (list.length l + ns + ms)) split_length
      ...  = 2 * l.length + ns + ms : by ring
      ...  ≤ 2 * l.length + ns + 4 * l.length * (nat.log 2 l.length - 1) : begin refine add_le_add_left _ (2 * l.length + ns), exact ms_bound, end
      ...  ≤ 2 * l.length + 4 * l.length * (nat.log 2 l.length - 1) + ns : by ring
      ...  ≤ 2 * l.length + 4 * l.length * (nat.log 2 l.length - 1) + 4 * (l.length + 1) * nat.log 2 l.length : begin refine add_le_add_left _ (2 * l.length + 4 * l.length * (nat.log 2 l.length - 1)), exact ns_bound, end
      ...  ≤ 8 * l.length * nat.log 2 (l.length) : begin
                                                     ring,
                                                     rw nat.mul_sub_left_distrib,
                                                     ring,
                                                     rw add_mul,
                                                     rw add_mul,
                                                     rw nat.mul_sub_right_distrib,
                                                     refine (add_le_add_iff_left (4 * 1 * l.length)).mp _,
                                                     rw ← add_assoc,
                                                     rw ← add_assoc,
                                                     rw ← add_assoc,
                                                     rw ← nat.add_sub_assoc four_log_l_length (4 * 1 * l.length),
                                                     rw add_comm (4 * 1 * l.length) (4 * nat.log 2 l.length * l.length),

                                                     rw nat.add_sub_assoc rfl.ge (4 * nat.log 2 l.length * l.length),

                                                     rw nat.sub_self (4 * 1 * l.length),
                                                     simp,
                                                     rw t_len_l_len,
                                                     ring,
                                                     rw add_mul,
                                                     rw add_mul,
                                                     rw mul_assoc,
                                                     rw mul_comm l.length (nat.log 2 l.length),
                                                     rw ← mul_assoc,
                                                     rw add_assoc,
                                                     refine (add_le_add_iff_left (8 * nat.log 2 l.length * l.length)).mpr _,

                                                     refine sum_2b (λ {xx yy : ℕ} , xx ≤ yy) (4 * nat.log 2 l.length) l.length _,
                                                     exact log_2_times (λ {xx yy : ℕ}, xx ≤ yy) l.length one_lt_l_length,
                                                    end
end

end counting
