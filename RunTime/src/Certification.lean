import data.bool
import data.list
import MergeSortDirect
import InsertionSortDirect

namespace counting

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

@[simp] def comparisons_insert (a : α) : list α → ℕ
| [] := 0
| (h :: t) := if a ≼ h then 0 else 1 + comparisons_insert t

#eval comparisons_insert (λ m n : ℕ , m ≤ n) 6 [1, 3, 4, 9]
-- 3

#eval comparisons_insert (λ m n : ℕ , m ≤ n) 5 [0, 2, 3, 6]
-- 3

def remove_prefix (a : α) : list α → list α
| [] := []
| (h :: t) := if a ≼ h
              then h :: t
              else remove_prefix t

#eval remove_prefix (λ m n : ℕ , m ≤ n) 2 [1, 2, 3, 4]
-- [2, 3, 4]

#eval remove_prefix (λ m n : ℕ , m ≤ n) 10 [4, 6, 7, 9]
-- []

@[simp] def comparisons_merge : list α → list α → ℕ
| []        ys        := 0
| xs        []        := 0
| (x :: xs) (y :: ys) := comparisons_insert r x (y :: ys) +
  match remove_prefix r x (y :: ys) with
  | [] := 0
  | rest_ys := 1 + comparisons_merge xs rest_ys
  end

theorem comparisons_insert_correct (a : α) : ∀ l : list α,
  (ordered_insert r a l).snd = comparisons_insert r a l :=
begin
  intro l,
  induction l,
  { simp, },
  { simp, split_ifs,
    { exact rfl, },
    { rw ← l_ih,
      cases (ordered_insert r a l_tl),
      unfold ordered_insert,
    }
  }
end

theorem comparisons_merge_correct : ∀ l₁ l₂ : list α,
  (merge r l₁ l₂).snd = comparisons_merge r l₁ l₂
| []         []         := begin simp, unfold merge, end
| []         (h₂ :: t₂) := begin simp, unfold merge, end
| (h₁ :: t₁) []         := begin simp, unfold merge, end
| (h₁ :: t₁) (h₂ :: t₂) :=
begin
  simp,
  unfold remove_prefix,
  unfold merge,
  split_ifs,
  { have ih := comparisons_merge_correct t₁ (h₂ :: t₂),
    cases (merge r t₁ (h₂ :: t₂)),
    unfold merge,
    simp at *,
    rw ih,
    ring,
  },
  have ih := comparisons_merge_correct (h₁ :: t₁) t₂,
  cases (merge r (h₁ :: t₁) t₂),
  unfold merge,
  simp at *,
  rw ih,
  cases t₂,
  { simp, refl, },
  simp, ring,
end


end counting
