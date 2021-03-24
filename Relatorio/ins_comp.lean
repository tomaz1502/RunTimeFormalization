def comparisons_insert (a : α) : list α → ℕ
| [] := 0
| (h :: t) := if a ≼ h
              then 1
              else 1 + comparisons_insert t
