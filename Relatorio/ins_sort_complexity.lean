theorem insertion_sort_complexity : ∀ l : list α,
  (insertion_sort r l).snd ≤ l.length * l.length :=
