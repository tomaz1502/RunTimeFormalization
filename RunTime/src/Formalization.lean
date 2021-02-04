import data.list.sort tactic

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting

@[simp] def ordered_insert (a : α) : list α → (list α × ℕ)
| []       := ([a], 0)
| (h :: t) := if a ≼ h then (a :: h :: t, 1)
                       else let (l', n) := ordered_insert t in (h :: l', n + 1)

@[simp] def insertion_sort : list α → (list α × ℕ)
| [] := ([], 0)
| (h :: t) := let (l', n) := (insertion_sort t) , (l'', m) := ordered_insert r h l'
              in (l'', n + m)

@[simp] def smaller_prefix (a : α) : list α → ℕ
| []       := 0
| (h :: t) := if a ≼ h then 0 else 1 + smaller_prefix t

end counting

theorem ordered_insert_linear (a : α) : ∀ l : list α, (counting.ordered_insert r a l).snd ≤ l.length :=
begin
  intro l,
  induction l,
  { simp, },
  { simp, split_ifs,
    { simp, },
    { cases (counting.ordered_insert r a l_tl),
      unfold counting.ordered_insert,
      simp,
      exact l_ih,
    }
  }
end

theorem ordered_insert_identification (a : α) : ∀ l : list α,
  (counting.ordered_insert r a l).fst = list.ordered_insert r a l := sorry

theorem counting_comparisons_ordered_insertion (a : α) : ∀ l : list α,
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

#print counting.insertion_sort._match_1

theorem insertion_sort_quadratic : ∀ l : list α, (counting.insertion_sort r l).snd ≤ (l.length * l.length) :=
begin
  intro l,
  induction l,
  { simp, },
  { simp,
    cases (counting.insertion_sort r l_tl) with sorted_tl ops,
    unfold counting.insertion_sort,
    have hh : (counting.ordered_insert r l_hd sorted_tl).snd ≤
       sorted_tl.length := ordered_insert_linear r l_hd sorted_tl,
    cases (counting.ordered_insert r l_hd sorted_tl),
    unfold counting.insertion_sort,
    have same_lengths : sorted_tl.length = l_tl.length :=
    begin
      induction sorted_tl,
      { sorry },
      { sorry }
    end,
    linarith,
  }
end

theorem insertion_sort_identification (a : α) : ∀ l : list α,
  (counting.insertion_sort r l).fst = list.insertion_sort r l := sorry
