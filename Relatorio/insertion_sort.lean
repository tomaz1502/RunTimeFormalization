def insert (a : α) : list α → list α
| []       := [a]
| (h :: t) := if a ≼ h then a :: h :: t
                       else h :: insert t

def insertion_sort : list α → list α
| []       := []
| (b :: l) := insert r b (insertion_sort l)
