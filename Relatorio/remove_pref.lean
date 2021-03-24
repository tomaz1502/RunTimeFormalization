def remove_prefix (a : α) : list α → list α
| [] := []
| (h :: t) := if a ≼ h
              then h :: t
              else remove_prefix t
