import data.list.sort tactic
import data.nat.log

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting

@[simp] def split : list α → (list α × list α × ℕ)
| []       := ([], [], 0)
| (a :: l) := let (l₁, l₂, n) := split l in (a :: l₂, l₁, n + 1)


theorem length_split_lt {a b} {l l₁ l₂ : list α} {n : ℕ} (h : split (a::b::l) = (l₁, l₂, n)) :
  list.length l₁ < list.length (a::b::l) ∧ list.length l₂ < list.length (a::b::l) :=
begin
  sorry
  -- cases e : split l with l₁' l₂',
  -- injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h, substs l₁ l₂,
  -- cases length_split_le e with h₁ h₂,
  -- exact ⟨nat.succ_le_succ (nat.succ_le_succ h₁), nat.succ_le_succ (nat.succ_le_succ h₂)⟩
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
  cases merge_sort l₁ with l₁' n₁,
  cases merge_sort l₂ with l₂' n₂,
  cases merge r l₁' l₂' with l' m,
  exact (l', m + n₁ + n₂ + n)
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf list.length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

theorem merge_complexity : ∀ l l' : list α , (merge r l l').snd ≤ l.length + l'.length
| []   []               := begin unfold merge, simp, end
| []   (h' :: t')       := begin unfold merge, simp, end
| (h :: t)    []        := begin unfold merge, simp, end
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

theorem merge_equivalence : ∀ l l' : list α , (merge r l l').fst = list.merge r l l' := sorry

theorem merge_sort_complexity : ∀ l : list α , (merge_sort r l).snd ≤ l.length * nat.log 2 l.length := sorry

theorem merge_sort_equivalence : ∀ l : list α , (merge_sort r l).fst = list.merge_sort r l := sorry

end counting
