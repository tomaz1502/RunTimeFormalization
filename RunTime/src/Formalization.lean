import data.list.sort
import data.int.basic

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

@[simp] def ordered_insert (a : α) : list α → (list α × ℕ)
| [] := ([a], 0)
| (b :: l) := if a ≼ b then (a :: b :: l, 1)
                       else let (l', n) := ordered_insert l in (b :: l', n + 1)

@[simp] def insertion_sort : list α → (list α × ℕ)
| [] := ([], 0)
| (a :: l) := let (l', n) := (insertion_sort l) , (l'', m) := ordered_insert r a l'
              in (l'', n + m)


-- theorem ordered_insert_linear (a : α) : ∀ l : list α, (ordered_insert r a l).snd ≤ l.length :=
-- begin
--   intros,
--   induction l,
--   { simp, },
--   {}
--  end
