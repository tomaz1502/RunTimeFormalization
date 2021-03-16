def split_extended : list α → (list α × list α × ℕ)
| []       := ([], [], 0)
| (h :: t) := let (l₁, l₂, n) := split_extended t
              in (h :: l₂, l₁, n + 1)

def merge_extended : list α → list α → (list α × ℕ)
| []       l'        := (l', 0)
| l        []        := (l,  0)
| (a :: l) (b :: l') := if a ≼ b
                        then let (l'', n) := merge_extended l (b :: l')
                             in (a :: l'', n + 1)
                        else let (l'', n) := merge_extended (a :: l) l'
                             in (b :: l'', n + 1)

def merge_sort_extended : list α → (list α × ℕ)
| []        := ([],  0)
| [a]       := ([a], 0)
| (a::b::l) := begin
  cases e : split_extended (a::b::l) with l₁ l₂n,
  cases l₂n with l₂ n,
  cases length_split_lt e with h₁ h₂,
  have ms₁ := merge_sort_extended l₁,
  have ms₂ := merge_sort_extended l₂,
  have merged := merge_extended r ms₁.fst ms₂.fst,
  have split_ops := (split_extended (a::b::l)).snd.snd,
  exact ( merged.fst , split_ops + ms₁.snd + ms₂.snd + merged.snd),
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf list.length nat.lt_wf⟩],
  dec_tac := tactic.assumption }
