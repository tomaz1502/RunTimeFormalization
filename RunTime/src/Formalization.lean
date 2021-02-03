import data.list.sort

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting

@[simp] def go_oi (h : α) (p : list α × ℕ) : (list α × ℕ) := (h :: p.fst, p.snd + 1)
-- | (l, n) := (b :: l, n + 1)

-- the second value in the output is the number of comparisons made
@[simp] def ordered_insert (a : α) : list α → (list α × ℕ)
| []       := ([a], 0)
| (h :: t) := if a ≼ h then (a :: h :: t, 0)
                       -- else go_oi h (ordered_insert t)
                       else let (l', n) := ordered_insert t in (h :: l', n + 1)

-- @[simp] def go_is (p₁ : (list α × ℕ)) : (list α × ℕ) :=

@[simp] def insertion_sort : list α → (list α × ℕ)
| [] := ([], 0)
-- | (h :: t) := go_is (insertion_sort t)
| (h :: t) := let (l', n) := (insertion_sort t) , (l'', m) := ordered_insert r h l'
              in (l'', n + m)

-- @[simp] def smaller_prefix (a : α) (l : list α) : ℕ := (list.take_while (λ m , m ≼ a) l).length
@[simp] def smaller_prefix (a : α) : list α → ℕ
| []       := 0
| (h :: t) := if a ≼ h then 0 else 1 + smaller_prefix t

end counting

theorem ordered_insert_linear (a : α) : ∀ l : list α, (counting.ordered_insert r a l).snd ≤ l.length
| [] := by simp
| (h :: t) :=
begin
  simp,
  split_ifs,
  { simp, },
  {  }
end

theorem ordered_insert_identification (a : α) : ∀ l : list α,
  (counting.ordered_insert r a l).fst = list.ordered_insert r a l := sorry

theorem counting_comparisons_oi (a : α) : ∀ l : list α,
  (counting.ordered_insert r a l).snd = counting.smaller_prefix (≼) a l
| []       := by simp
| (h :: t) :=
begin
  simp,
  split_ifs,
  { simp },
  { rw counting_comparisons_oi t,
    exact add_comm (counting.smaller_prefix r a t) 1
  }
end

theorem insertion_sort_quadratic : ∀ l : list α, (counting.insertion_sort r l).snd ≤ l.length * l.length
| []       := by simp
| (h :: t) := sorry

theorem insertion_sort_identification (a : α) : ∀ l : list α,
  (counting.insertion_sort r l).fst = list.insertion_sort r l := sorry
