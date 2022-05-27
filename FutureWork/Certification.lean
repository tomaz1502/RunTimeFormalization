/-
Copyright (c) 2022 Tomaz Gomes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Tomaz Gomes.
-/
import data.bool
import data.list
import MergeSort.MergeSort
import InsertionSort

namespace Timed

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

@[simp] def comparisons_insert (a : α) : list α → ℕ
| [] := 0
| (h :: t) := if a ≼ h then 1 else 1 + comparisons_insert t

#eval comparisons_insert (λ m n : ℕ , m ≤ n) 6 [1, 3, 4, 9]
-- 3

#eval comparisons_insert (λ m n : ℕ , m ≤ n) 5 [0, 2, 3, 6]
-- 3

@[simp] def remove_prefix (a : α) : list α → list α
| [] := []
| (h :: t) := if a ≼ h then h :: t
              else remove_prefix t

#eval remove_prefix (λ m n : ℕ , m ≤ n) 2 [1, 2, 3, 4]
-- [2, 3, 4]

#eval remove_prefix (λ m n : ℕ , m ≤ n) 10 [4, 6, 7, 9]
-- []

@[simp] def comparisons_merge : list α → list α → ℕ
| []        ys        := 0
| xs        []        := 0
| (x :: xs) (y :: ys) := comparisons_insert r x (y :: ys) +
                         comparisons_merge xs (remove_prefix r x ys)

def l₁ : list ℕ := [8, 1, 3]
def l₂ : list ℕ := [14, 5, 6]

#eval comparisons_merge (λ m n : ℕ, m ≤ n) l₁ l₂
#eval prod.snd (merge (λ m n : ℕ, m ≤ n) l₁ l₂)

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
      rw add_comm,
    }
  }
end


theorem comparisons_merge_correct : ∀ l₁ l₂ : list α,
  (merge r l₁ l₂).snd = comparisons_merge r l₁ l₂
| []         []         := begin simp only [comparisons_merge], unfold merge, end
| []         (h₂ :: t₂) := begin simp only [comparisons_merge], unfold merge, end
| (h₁ :: t₁) []         := begin simp only [comparisons_merge], unfold merge, end
| (h₁ :: t₁) (h₂ :: t₂) :=
begin
  simp only [comparisons_insert, comparisons_merge, remove_prefix, merge],
  split_ifs,
  { have ih := comparisons_merge_correct t₁ (h₂ :: t₂),
    cases (merge r t₁ (h₂ :: t₂)) with _ cnt,

    unfold merge,
    simp at *,
    
    cases t₂,

    { simp, rw ih, simp, },
    rw ← ih,
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


end Timed
