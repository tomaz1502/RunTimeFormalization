import data.list.sort tactic
import data.nat.log

import tactic.monotonicity

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting


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


#check le_trans

theorem add_le_right {a b c d : ℕ} : d ≤ b → a + b ≤ c → a + d ≤ c := by omega



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

theorem merge_sort_complexity : ∀ l : list α , (merge_sort r l).snd ≤ l.length * nat.log 2 l.length
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

  -- have ns_bound : 2 * ns ≤ t.length + 3 := sorry,

  have ms_bound : 2 * ms ≤ (t.length + 2) * nat.log 2 (t.length + 2) :=
  begin
    rw t_len_l_len,
    rw h₂ at ih₂,
    simp at ih₂,
    sorry,
  end,


  have l₁s_length : l₁s.length ≤ t.length + 1 :=
  begin
    have l₁s_id : l₁s = (merge_sort r l₁).fst := by rw h₁,
    rw l₁s_id,
    rw merge_sort_equivalence r l₁,
    rw list.length_merge_sort,

    cases length_split_lt hs with l₁_length _,

    exact nat.lt_succ_iff.mp l₁_length,
  end,

  have l₂s_length : l₂s.length ≤ t.length + 1 :=
  begin
    have l₂s_id : l₂s = (merge_sort r l₂).fst := by rw h₂,
    rw l₂s_id,
    rw merge_sort_equivalence r l₂,
    rw list.length_merge_sort,

    cases length_split_lt hs with _ l₂_length,

    exact nat.lt_succ_iff.mp l₂_length,
  end,

  simp,

  calc t.length + 1 + 1 + ns + ms + (merge r l₁s l₂s).snd
           ≤ t.length + 1 + 1 + ns + ms + (l₁s.length + l₂s.length)     : add_le_add_left (merge_complexity r l₁s l₂s) (t.length + 1 + 1 + ns + ms)
       ... ≤ t.length + 1 + 1 + ns + ms + (t.length + 1 + t.length + 1) : begin refine add_le_add_left _ (t.length + 1 + 1 + ns + ms), rw add_assoc, exact add_le_add l₁s_length l₂s_length, end
       ... ≤ (t.length + 1 + 1) * nat.log 2 (t.length + 1 + 1)        : sorry

end

end counting
