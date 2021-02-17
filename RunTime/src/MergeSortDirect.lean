import data.list.sort tactic
import data.nat.log

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace counting


@[simp] def split : list α → (list α × list α × ℕ)
| []       := ([], [], 0)
| (h :: t) := let (l₁, l₂, n) := split t in (h :: l₂, l₁, n + 1)

theorem split_equivalence : ∀ (l : list α) ,
  (split l).fst = (list.split l).fst ∧ (split l).snd.fst = (list.split l).snd
| [] := by simp
| (h :: t) :=
begin
  simp,

  have ih := split_equivalence t,
  cases ih with ih_fst ih_snd,

  cases (split t) with t_left₁ t_right₁,
  cases t_right₁ with t_right₁ _,
  unfold split,

  cases t.split with t_left₂ t_right₂,
  unfold list.split,
  simp,

  exact ⟨ ih_snd, ih_fst ⟩,
end

theorem length_split_lt {a b} {l l₁ l₂ : list α} {n : ℕ} (h : split (a::b::l) = (l₁, l₂, n)) :
  list.length l₁ < list.length (a::b::l) ∧ list.length l₂ < list.length (a::b::l) :=
begin
  have eq_mathlib : l₁ = (a::b::l).split.fst ∧ l₂ = (a::b::l).split.snd :=
  begin
    have l₂_n_id : (l₂, n) = (split (a :: b :: l)).snd := (congr_arg prod.snd h).congr_right.mpr rfl,
    have l₂_id : l₂ = (split (a :: b :: l)).snd.fst := (congr_arg prod.fst l₂_n_id).congr_right.mp rfl,
    have l₁_id : l₁ = (split (a :: b :: l)).fst := (congr_arg prod.fst h).congr_right.mpr rfl,
    have split_eq := split_equivalence  (a :: b :: l),
    cases split_eq,

    rw split_eq_left at l₁_id,
    rw split_eq_right at l₂_id,

    exact ⟨ l₁_id , l₂_id ⟩,
  end,
  cases eq_mathlib,
  have reconstruct : (a::b::l).split = (l₁, l₂) :=
  begin
    rw eq_mathlib_left,
    rw eq_mathlib_right,
    exact prod.ext rfl rfl,
  end ,
  exact list.length_split_lt reconstruct,
end

def merge : list α → list α → (list α × ℕ)
| []       l'        := (l', 0)
| l        []        := (l,  0)
| (a :: l) (b :: l') := if a ≼ b
                        then let (l'', n) := merge l (b :: l') in (a :: l'', n + 1)
                        else let (l'', n) := merge (a :: l) l' in (b :: l'', n + 1)

include r

def merge_sort : list α → (list α × ℕ)
| []        := ([],  0)
| [a]       := ([a], 0)
| (a::b::l) := begin
  cases e : split (a::b::l) with l₁ l₂n,
  cases l₂n with l₂ n,
  cases length_split_lt e with h₁ h₂,
  cases merge_sort l₁ with l₁' n₁,
  cases merge_sort l₂ with l₂' n₂,
  cases merge r l₁' l₂' with l' m,
  exact (l', m + n₁ + n₂ + n)
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf list.length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

theorem merge_complexity : ∀ l l' : list α , (merge r l l').snd ≤ l.length + l'.length
| []   []               := begin unfold merge, simp, end
| []   (h' :: t')       := begin unfold merge, simp, end
| (h :: t)    []        := begin unfold merge, simp, end
| (h₁ :: t₁) (h₂ :: t₂) :=
begin
  unfold merge, split_ifs,
  { have hh := merge_complexity t₁ (h₂ :: t₂),
    cases (merge r t₁ (h₂ :: t₂)),
    unfold merge,
    simp at hh,
    simp,
    linarith,
  },
  { have hh := merge_complexity (h₁ :: t₁) t₂,
    cases (merge r (h₁ :: t₁) t₂),
    unfold merge,
    simp at hh,
    simp,
    linarith,
  }
end

theorem merge_equivalence : ∀ l l' : list α , (merge r l l').fst = list.merge r l l'
| []       []         := begin unfold merge, unfold list.merge, end
| []       (h' :: t') := begin unfold merge, unfold list.merge, end
| (h :: t) []         := begin unfold merge, unfold list.merge, end
| (h :: t) (h' :: t') :=
begin
  unfold merge,
  split_ifs,
  { have ih := merge_equivalence t (h' :: t'),
    cases (merge r t (h' :: t')),
    unfold merge,

    unfold list.merge,
    split_ifs,
    exact ⟨ rfl, ih ⟩,
  },
  { have ih := merge_equivalence (h :: t) t',
    cases (merge r (h :: t) t'),
    unfold merge,

    unfold list.merge,
    split_ifs,
    exact ⟨ rfl, ih ⟩,
  }
end

theorem merge_sort_complexity : ∀ l : list α , (merge_sort r l).snd ≤ l.length * nat.log 2 l.length := sorry

theorem merge_sort_equivalence : ∀ l : list α , (merge_sort r l).fst = list.merge_sort r l := sorry

end counting
