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

    @[simp] def untime {n : ℕ} {A : Sort u} : A inTime n → A
    | (box a) := a

    def bind {A : Sort u} {B : Sort v} {n m : ℕ} : A inTime n → (A → B inTime m) → B inTime (n + m)
    | (box a) f := box (untime (f a))

    def pure {A : Sort u} : A → A inTime 0 := box

    infixl ` >>= `:55 := bind

    def fmap {A : Sort u} {B : Sort v} {n : ℕ} : (A → B) → A inTime n → B inTime n
    | f (box a) := box (f a)
infixl ` <$> `:55 := fmap

    def eqBound {A : Sort u} {n m : ℕ} : (n = m) → A inTime n → A inTime m
    | _ (box a) := box a

    def relaxBound {A : Sort u} {n m : ℕ} : (n ≤ m) → A inTime n → A inTime m
    | _ (box a) := box a

    axiom timedQuery' : ∀ (a b : α), psum (r a b) (r b a) inTime 1

end timeMonad

open timeMonad

namespace insertionSort

/- theorem ff : ∀ {A : Sort u} (a : A),  untime (pure a) = a := -/
/- begin -/
/-   intros, -/
  
/- end -/

noncomputable def insert (a : α) : Π (xs : list α) , list α inTime xs.length
| []         := pure [a]
| (x :: xs') := have eqProof : (1 + xs'.length = (x :: xs').length),
                by { simp, exact add_comm 1 xs'.length, },
  eqBound eqProof $ timedQuery' r a x >>= λ cmp,
                   match cmp with
                     | (psum.inl ax) := relaxBound bot_le $ pure (a :: x :: xs')
                     | (psum.inr xa) := (λ z , x :: z) <$> insert xs'
                   end
 
noncomputable def insertion_sort : Π (xs : list α) , list α inTime (xs.length * xs.length)
| []         := pure []
| (x :: xs') := have time_bound: xs'.length * xs'.length ≤ (x :: xs').length * xs'.length,
                by { simp, rw mul_comm (xs'.length + 1) xs'.length, exact le_self_add, },
  relaxBound time_bound (insertion_sort xs') >>=
                (λ sorted_xs' , 
                  let same_lengths : sorted_xs'.length = xs'.length := sorry,
                      cons_inc_size: xs'.length ≤ (x :: xs').length := nat.le.intro rfl
                  in relaxBound cons_inc_size (eqBound same_lengths (insert r x sorted_xs')))
                 
theorem insertion_sort_preserves_length :
  ∀ (xs : list α), xs.length = (untime (insertion_sort r xs)).length
| [] := begin simp, unfold insertion_sort, unfold timeMonad.pure, refl,  end
| (x :: xs') :=
begin
  simp,
  have ih := insertion_sort_preserves_length xs',
  cases insertion_sort r (x :: xs') with sorted_xs',
  simp,
  sorry,
end

end insertionSort
