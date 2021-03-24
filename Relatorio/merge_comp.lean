def comparisons_merge : list α → list α → ℕ
| []        ys        := 0
| xs        []        := 0
| (x :: xs) (y :: ys) := comparisons_insert r x (y :: ys) +
                         comparisons_merge xs (remove_prefix r x)
