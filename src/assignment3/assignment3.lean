import data.real.basic

/-
FIRST EXERCISE: Strict monotonicity

Section 3.1 of MIL discusses the `monotone` predicate. There is also a strict
version. Prove the theorems below, *and* come up with suitable names
(in other words, replace `example` with `theorem foo`.)

(Don't use any library theorems about `strict_mono` or `monotone`! You should
only use basic properties of orderings.)
-/

#print monotone. 
#print strict_mono. 

namespace strict_mono_exercise

variables (f : ℝ → ℝ) (g : ℝ → ℝ)

theorem strict_mono_add (hf : strict_mono f) (hg : strict_mono g) : strict_mono (f + g) :=
begin
  intros a b hab,
  apply add_lt_add,
  apply hf hab,
  apply hg hab,
end

-- You'll have to guess at the name of a theorem for this one.
theorem strict_mono_scalar_mul (c : ℝ) (hf : strict_mono f) (hc : 0 < c) :
  strict_mono (λ x, c * f x) :=
begin
  intros a b hab,
  rw mul_lt_mul_left,
  exact hf hab,
  exact hc,
end

-- This is trickier than you might think. Use `by_cases h : a = b` to split
-- on cases whether `a = b`. You can also use `lt_of_le_of_ne`.

theorem mono_of_strict_mono (hf : strict_mono f) : monotone f :=
begin
  intros a b hab,
  by_cases h : a = b,
  {
    -- Case a = b:
    rw h,
  },
  {
    -- Case a ≠ b:
    apply le_of_lt,
    apply hf,
    apply lt_of_le_of_ne hab h,
  }
end

/-
The following (trivial) example shows how to use trichotomy. You do not need
to fully understand the pattern now; you can take it as a black box.
-/

example (x1 x2 : ℝ) : x1 ≤ x2 ∨ x2 < x1 :=
begin
  rcases trichotomous_of (<) x1 x2 with h | h | h,
  { -- In this case, we have `h : x1 < x2`.
    left,
    apply le_of_lt h },
  { -- In this case, we have `h : x1 = x2`.
    left,
    rw h },
  -- In this case, we have `h : x2 < x1`
  right,
  exact h
end

open function

/-
Here is an example that shows that `x ↦ x + 1` is injective.
-/

example : injective (λ x, x + 1) :=
begin
  intros x1 x2 h,
  dsimp at h,  -- this makes `h` more readable
  exact add_right_cancel h
end

/-
Show that every strictly monotone function is injective.
-/

theorem injective_of_strict_mono (hf : strict_mono f) : injective f :=
begin
  intros a b,
  rcases trichotomous_of (<) a b with h | h | h,
  {
    -- Case a < b:
    contrapose,
    intro,
    apply ne_of_lt,
    apply hf h
  },
  {
    -- Case a = b:
    intro,
    apply h
  },
  {
    -- Case a > b:
    contrapose,
    intro,
    apply ne_of_gt,
    apply hf h
  },
end

end strict_mono_exercise

/-
SECOND EXERCISE: Galois connections

Given `α` with a partial order, a *closure operator* `cl : α → α` has the
following properties:

- `cl` is monotone
- `cl` is increasing, in the sense that for every `a : α`, `a ≤ cl a`
- `cl` is idempotent, in the sense that for every `a : α`, `cl (cl a) = cl a`.

Given `α` and `β` with partial orders, a *Galois connection* is a pair of
monotone functions `f : α → β` and `g : β → α` satisfying the following:

  For every `a` and `b`, `f a ≤ b` if and only if `a ≤ g b`.

You can read more about these here:

  https://en.wikipedia.org/wiki/Closure_operator
  https://en.wikipedia.org/wiki/Galois_connection

The exercises below ask you to show that if `f` and `g` form a Galois
connection, then `g ∘ f` is a closure operator, and `f ∘ g` is a closure
operator on the reverse order.
-/

namespace galois_connection_exercise

variables {α β : Type*} [partial_order α] [partial_order β]
variable  {f : α → β}
variable  {g : β → α}
variable  mono_f : monotone f
variable  mono_g : monotone g
variable  adj1 : ∀ a b, f a ≤ b → a ≤ g b
variable  adj2 : ∀ a b, a ≤ g b → f a ≤ b

section
-- you can use these:
include mono_f mono_g

theorem mono_gf : monotone (g ∘ f) :=
begin
  intros a b hab,
  apply mono_g (mono_f hab)
end

theorem mono_fg : monotone (f ∘ g) :=
begin
  intros a b hab,
  apply mono_f (mono_g hab)
end

end

section
include adj1

theorem increasing_gf : ∀ a, a ≤ g (f a) :=
begin
  intros,
  apply adj1,
  refl
end
end

section
include adj2

theorem decreasing_fg : ∀ b, f (g b) ≤ b :=
begin
  intros,
  apply adj2,
  refl
end
end

include mono_f mono_g adj1 adj2

/-
Unfortunately, for the theorems you just proved, you have to give the
hypotheses as arguments.
-/

#check mono_fg mono_f mono_g
#check mono_gf mono_f mono_g
#check increasing_gf adj1
#check decreasing_fg adj2

theorem idempotent_gf : ∀ a, g (f (g (f a))) = g (f a) :=
begin
  intros,
  apply ge_antisymm,
  {
    -- Case g (f a) ≤ g (f (g (f a))):
    -- This is equivalent to (g ∘ f) a ≤ (g ∘ f) (g (f a)).
    apply mono_gf mono_f mono_g,
    -- Now, all that remains to show is that a ≤ g (f a), which is proven above as increasing_gf.
    apply increasing_gf adj1
  },
  {
    -- Case g (f (g (f a))) ≤ g (f a):
    apply adj1,
    -- Now want to show that f (g (f (g (f a)))) ≤ f a.
    apply le_trans,
    apply decreasing_fg adj2, -- f (g (f (g (f a)))) ≤ (f (g (f a)))
    apply decreasing_fg adj2  -- f (g (f a)) ≤ f a
  },
end

theorem idempotent_fg : ∀ b, f (g (f (g b))) = f (g b) :=
begin
  intros,
  apply le_antisymm,
  {
    -- Case f (g (f (g b))) ≤ f (g b):
    -- This is equivalent to (f ∘ g) (f (g b)) ≤ (f ∘ g) b.
    apply mono_fg mono_f mono_g,
    -- Now, all that remains to prove is that f (g b) ≤ b, which is proven above as decreasing_fg,
    apply decreasing_fg adj2
  },
  {
    -- Case f (g b) ≤ f (g (f (g b))):
    apply adj2,
    -- Now want to show that g b ≤ g (f (g (f (g b)))).
    apply le_trans,
    apply increasing_gf adj1,
    apply increasing_gf adj1,
  }
end

end galois_connection_exercise

/-
THIRD EXERCISE: convergence to infinity

Below, `to_infinity f` expresses that `f x` approaches infinity as
`x` approaches infinity.

The properties below are analogous to properties proved in Sections 3.2
and 3.6 in Mathematics in Lean. They involve the universal and existential
quantifiers (both no other logical connectives).
-/

def to_infinity (f : ℝ → ℝ) := ∀ b, ∃ x₀, ∀ x, x₀ ≤ x → b < f x

-- hint: you can use `linarith` at the end
example (f : ℝ → ℝ) (r : ℝ) (hf : to_infinity f) :
  to_infinity (λ x, f x + r) :=
begin
  unfold to_infinity,
  intro b,
  cases hf (b - r) with x₀ h2,
  use x₀,
  intros x hx₀_le_x,
  specialize h2 x hx₀_le_x,
  linarith
end

-- hint: `div_lt_iff'` is useful here
example (f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hf : to_infinity f) :
  to_infinity (λ x, r * f x) :=
begin
  unfold to_infinity,
  intro b,
  cases hf (b / r) with x₀ h2,
  use x₀,
  intros x hx₀_le_x,
  specialize h2 x hx₀_le_x,
  have h3 : b < f x * r,
  {
    rw ←div_lt_iff hr,
    apply h2
  },
  linarith
end

-- hint: you can use `le_max_left` and `le_max_right`
example (f g : ℝ → ℝ) (hf : to_infinity f) (hg : to_infinity g) :
  to_infinity (f + g) :=
begin
  sorry
end
