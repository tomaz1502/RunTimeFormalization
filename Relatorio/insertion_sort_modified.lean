def insert_extended (a : α) : list α → (list α × ℕ)
| []       := ([a], 0)
| (h :: t) := if a ≼ h then (a :: h :: t, 0)
                       else let (l', n) := insert_extended t
                            in (h :: l', 1 + n)

def insertion_sort_extended : list α → (list α × ℕ)
| [] := ([], 0)
| (h :: t) := let (l', n) := (insertion_sort_extended t) ,
                  (l'', m) := insert_extended r h l'
              in (l'', n + m)
