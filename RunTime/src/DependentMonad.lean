import data.list.sort

-- set_option trace.eqn_compiler.elim_match true

universe variables u v
variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace timeMonad

    inductive Timed (A : Sort u) (n : ℕ) : Sort (u + 1)
    | box : A → Timed

    open Timed

    infixl ` inTime `:55 := Timed

    def untime {n : ℕ} {A : Sort u} : A inTime n → A
    | (box a) := a

    def bind {A : Sort u} {B : Sort v} {n m : ℕ} : A inTime n → (A → B inTime m) → B inTime (n + m)
    | (box a) f := box (untime (f a))

    def return {A : Sort u} : A → A inTime 0 := box

    infixl ` >>= `:55 := bind

    def fmap {A : Sort u} {B : Sort v} {n : ℕ} : (A → B) → A inTime n → B inTime n
    | f (box a) := box (f a)

    infixl ` <$> `:55 := fmap

    def eqBound {A : Sort u} {n m : ℕ} : (n = m) → A inTime n → A inTime m
    | _ (box a) := box a

    def relaxBound {A : Sort u} {n m : ℕ} : (n ≤ m) → A inTime n → A inTime m
    | _ (box a) := box a


    def timedQuery (a b : α) : (psum (r a b) (r b a)) inTime 1 :=
      if r a b
      then box (psum.inl sorry)
      else box (psum.inr sorry)

variables a b : α
variable z : r a b
#check is_true (z)

end timeMonad

open timeMonad

-- namespace insertionSort

def insert (a : α) : Π (xs : list α) , (list α) inTime xs.length
| []         := return [a]
| (x :: xs') := have eqProof : (1 + xs'.length = (x :: xs').length),
                by { simp, exact add_comm 1 xs'.length, },
  eqBound eqProof $ timedQuery r a x >>= λ cmp,
                   match cmp with
                     | (psum.inl ax) := relaxBound bot_le $ return (a :: x :: xs')
                     | (psum.inr xa) := (λ z , x :: z) <$> insert xs'
                   end

-- end insertionSort
