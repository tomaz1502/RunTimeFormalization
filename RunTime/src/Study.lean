import data.list.sort
import data.nat.basic

#check list.ordered_insert

-- Studying how to implement dependent types in lean
namespace study

variable α : Type


inductive fin : ℕ → Type
| finZero {n : ℕ} : fin (n + 1)
| finSucc {n : ℕ} : fin n → fin (n + 1)

#check fin.finZero

inductive vec : Type → ℕ → Type 1
| vecNil  {α : Type} : vec α 0
| vecCons {α : Type} {n : ℕ} : vec α n → α → vec α (n + 1)

#check @vec.vecNil α
#check @vec.vecCons α 0
#check nat

-- is there a better way to write this function?
def safeLookUp (α : Type) : ∀ {n : ℕ} , vec α (n + 1) → fin (n + 1) → α
| n            (vec.vecCons v a) fin.finZero     := a
| (nat.succ n) (vec.vecCons v a) (fin.finSucc i) := safeLookUp v i

end study

-- Counting steps for computation
namespace countingMonad

inductive inTime : Prop → ℕ → Prop
| box {α : Prop} {n : ℕ} : inTime α n

axiom compare : ∀ {α : Type} [has_le α] {x y : α},
  inTime (x ≤ y \/ y ≤ x) 1

def comp {α : Type} [has_le α] (x y : α) := x ≤ y

lemma ll : ∀ {α : Type} {x y : α} [s : has_le α], inTime (@comp α s x y) 1 :=
begin
  intros,
  sorry,
end

-- Another possibility?
inductive inTime' {α β : Type} : (α → β) → ℕ → Prop
| box {f : α → β} {n : ℕ} : inTime' f n

def f := (λ x y z : ℕ , x + y + z)

#check f

axiom constantForSum : inTime' f 1

#check list.nil

inductive InsideOf {α : Type} : α → list α → list α → Type
| here  {x : α}   {xs : list α}    : InsideOf x xs (x :: xs)
| there {x y : α} {xs ys : list α} : InsideOf x xs ys → InsideOf x (y :: xs) (y :: ys)


end countingMonad

@[simp] def f (n : ℕ) : ℕ := let m := 2 * n in m

theorem please_help : ∀ n, even (f n) :=
begin
  intros,
  induction n,
  { use 0,
    exact rfl,
  },
  {
    rename n_n n',
    obtain ⟨a, b⟩ := n_ih,
    simp,
    use n'.succ,
  }
end

def g : ℕ → ℕ
| 0 := 0
| (n + 1) := n

lemma l : ∀ x y : ℕ , g x = g y :=
begin
  intros,
  have h : x = 0 := sorry,
  rw g, bb
end
