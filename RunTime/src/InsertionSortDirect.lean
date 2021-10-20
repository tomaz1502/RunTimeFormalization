import data.list.sort tactic
import data.nat.log

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting

@[simp] def ordered_insert (a : α) : list α → (list α × ℕ)
| []       := ([a], 0)
| (h :: t) := if a ≼ h then (a :: h :: t, 1)
                       else let (l', n) := ordered_insert t in (h :: l', n + 1)

#eval ordered_insert (λ m n : ℕ , m ≤ n) 2 [5, 3, 1, 4]
-- ([2, 5, 3, 1, 4], 0)

#eval ordered_insert (λ m n : ℕ , m ≤ n) 9 [1, 0, 8]
-- ([1, 0, 8, 9], 3)

@[simp] def insertion_sort : list α → (list α × ℕ)
| [] := ([], 0)
| (h :: t) := let (l', n) := (insertion_sort t) , (l'', m) := ordered_insert r h l'
              in (l'', n + m)

#eval insertion_sort (λ m n : ℕ , m ≤ n) [1, 2, 3, 4, 5]
-- ([1, 2, 3, 4, 5], 0)

#eval insertion_sort (λ m n : ℕ , m ≤ n) [5, 4, 3, 2, 1]
-- ([1, 2, 3, 4, 5], 10)


theorem ordered_insert_complexity (a : α) :
  ∀ l : list α, (ordered_insert r a l).snd ≤ l.length :=
begin
  intro l,
  induction l,
  { simp, },
  { simp, split_ifs,
    { simp, },
    { cases (ordered_insert r a l_tl),
      unfold ordered_insert,
      linarith,
    }
  }
end

theorem ordered_insert_equivalence (a : α) : ∀ l : list α,
  (ordered_insert r a l).fst = list.ordered_insert r a l :=
begin
  intro l,
  induction l,
  { simp, },
  { simp, split_ifs,
    { simp, },
    { cases (ordered_insert r a l_tl),
      unfold ordered_insert,
      simp,
      exact l_ih,
    }
  }
end

theorem ordered_insert_length (a : α) : ∀ l : list α,
  (ordered_insert r a l).fst.length = l.length + 1 :=
begin
  intro l,
  rw ordered_insert_equivalence r a l,
  exact list.ordered_insert_length r l a,
end

theorem insertion_sort_preserves_length : ∀ l : list α,
  (insertion_sort r l).fst.length = l.length :=
begin
  intro l,
  induction l,
  { simp, },
  { simp,
    cases (insertion_sort r l_tl) with sorted_tl _,
    unfold insertion_sort,
    have ordered_length :
      (ordered_insert r l_hd sorted_tl).fst.length = sorted_tl.length + 1 :=
      ordered_insert_length r l_hd sorted_tl,
    cases (ordered_insert r l_hd sorted_tl) with sorted_list _,
    unfold insertion_sort,
    rw ordered_length,
    rw l_ih,
  }
end

theorem insertion_sort_complexity : ∀ l : list α, (insertion_sort r l).snd ≤ l.length * l.length :=
begin
  intro l,
  induction l,
  { simp, },
  { simp,
    have same_lengths : (insertion_sort r l_tl).fst.length = l_tl.length :=
      insertion_sort_preserves_length r l_tl,
    cases (insertion_sort r l_tl) with sorted_tl ops,
    unfold insertion_sort,
    have hh : (ordered_insert r l_hd sorted_tl).snd ≤
       sorted_tl.length := ordered_insert_complexity r l_hd sorted_tl,
    cases (ordered_insert r l_hd sorted_tl),
    unfold insertion_sort,
    linarith,
  }
end

theorem insertion_sort_equivalence (a : α) : ∀ l : list α,
  (insertion_sort r l).fst = list.insertion_sort r l :=
begin
  intro l,
  induction l,
  { simp, },
  { simp,
    rw ← l_ih,
    cases insertion_sort r l_tl,
    unfold insertion_sort,
    rw ← ordered_insert_equivalence r l_hd fst,
    cases ordered_insert r l_hd fst,
    unfold insertion_sort,
  }
end

end counting
