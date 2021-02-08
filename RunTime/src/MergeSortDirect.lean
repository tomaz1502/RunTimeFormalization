import data.list.sort tactic
import data.nat.log

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting

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
  cases e : list.split (a::b::l) with l₁ l₂,
  cases list.length_split_lt e with h₁ h₂,
  cases merge_sort l₁ with l₁' n₁,
  cases merge_sort l₂ with l₂' n₂,
  cases merge r l₁' l₂' with l' m,
  exact (l', m + n₁ + n₂)
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf list.length nat.lt_wf⟩],
  dec_tac := tactic.assumption }


#eval nat.log 2 8

theorem merge_complexity : ∀ l l' : list α , (merge r l l').snd ≤ min l.length l'.length := sorry

theorem merge_identification : ∀ l l' : list α , (merge r l l').fst = list.merge r l l' := sorry

theorem merge_sort_complexity : ∀ l : list α , (merge_sort r l).snd ≤ l.length * nat.log 2 l.length := sorry

theorem merge_sort_identification : ∀ l : list α , (merge_sort r l).fst = list.merge_sort r l := sorry

end counting
