inductive Nat : Type
| zero : Nat
| succ : Nat → Nat

@[simp] def add : Nat → Nat → Nat
| Nat.zero     n := n
| (Nat.succ m) n := Nat.succ (add m n)

lemma add_zero : ∀ m : Nat , add m Nat.zero = m
| Nat.zero     := by refl
| (Nat.succ m) := by { simp, exact add_zero m }

lemma add_succ : ∀ m n : Nat , add m (Nat.succ n) = Nat.succ (add m n)
| Nat.zero     n := by refl
| (Nat.succ m) n := by { simp, exact add_succ m n, }

theorem add_comm : ∀ m n : Nat , add m n = add n m
| m (Nat.zero)   := by { simp, exact add_zero m, }
| m (Nat.succ n) := by { simp, rw ← add_comm m n, exact add_succ m n, }
