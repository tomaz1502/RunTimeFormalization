def ordered_insert (a : α) : list α → list α
| []       := [a]
| (h :: t) := if a ≼ h then a :: h :: t
                       else h :: ordered_insert t

def insertion_sort : list α → list α
| []       := []
| (b :: l) := ordered_insert r b (insertion_sort l)
