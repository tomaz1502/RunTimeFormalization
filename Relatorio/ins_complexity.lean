theorem insert_complexity (a : α) :
  ∀ l : list α, (insert r a l).snd ≤ l.length
