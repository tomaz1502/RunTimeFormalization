import data.list.sort
import data.int.basic

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

@[simp] def ordered_insert (a : α) : list α → (list α × ℕ)
| [] := ([a], 0)
| (b :: l) := if a ≼ b then (a :: b :: l, 1)
                       else let (l', n) := ordered_insert l in (b :: l', n + 1)

theorem ordered_insert_linear (a : α) : ∀ l : list α, (ordered_insert r a l).snd ≤ l.length :=
begin
  intros,
  induction l,
  { simp, },
  {}
 end



theorem nineteen_dvd (a : ℤ) : 19 ∣ a ↔ 19 ∣ 4 * a :=
begin
  split,
  { intro h,
    exact dvd_mul_of_dvd_right h 4
  },
  { sorry, }

end


theorem nineteen_dvd' (a b : ℤ) : 19 ∣ 100 * a + b ↔ 19 ∣ a + 4 * b :=
sorry
