import data.list.sort

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

@[simp] def go (b : α) (l : list α × ℕ) : (list α × ℕ) := (b :: l.fst, l.snd + 1)

-- the second value in the output is the number of comparisons made
@[simp] def ordered_insert (a : α) : list α → (list α × ℕ)
| [] := ([a], 0)
| (b :: l) := if a ≼ b then (a :: b :: l, 1)
                       else go b (ordered_insert l)
                       -- else let (l', n) := ordered_insert l in (b :: l', n + 1)

@[simp] def insertion_sort : list α → (list α × ℕ)
| [] := ([], 0)
| (a :: l) := let (l', n) := (insertion_sort l) , (l'', m) := ordered_insert r a l'
              in (l'', n + m)


theorem ordered_insert_linear (a : α) : ∀ l : list α, (ordered_insert r a l).snd ≤ l.length
| [] := by simp
| (b :: l) :=
begin
  simp,
  split_ifs,
  { simp, },
  { have ih : (ordered_insert r a l).snd + 1 ≤ l.length + 1 := nat.pred_le_iff.mp (ordered_insert_linear l),
    refine le_trans _ ih,
    refine eq.ge _,
    exact rfl,
  }
end
