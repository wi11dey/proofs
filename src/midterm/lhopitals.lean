import data.real.basic
import data.real.sqrt

namespace lhopitals

-- NOTE: Assignment 4/5 has an incorrect ε-δ definition of a limit!
def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - b| < ε

def continuous (f : ℝ → ℝ) := ∀ a, approaches_at f (f a) a

example (δ : ℝ) (h : δ > 0) : ¬(δ ≤ 0) :=
begin
  exact not_le.mpr h,
end

def derivative_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) := 
  approaches_at (λ x, (f x - f a)/(x - a)) b a

-- This is my proof from Assignment 4, Exercise 3a:
theorem approaches_at_add_right (f : ℝ → ℝ) {a b c: ℝ}
    (hf : approaches_at f b a) :
  approaches_at (λ x, f x + c) (b + c) a :=
begin
  unfold approaches_at,
  intros ε hε,
  unfold approaches_at at hf,
  cases (hf ε hε) with δ hf,
  cases hf with hδ hf,
  use δ,
  split,
  { exact hδ },
  intros x hx_a_δ,
  ring_nf,
  exact hf x hx_a_δ
end

lemma approaches_at_zero (f : ℝ → ℝ) (b : ℝ) (a : ℝ)
    (hf : approaches_at f b a) :
  approaches_at (λ x, f x - b) 0 a :=
begin
  have : approaches_at (λ x, f x + (-b)) (b + (-b)) a,
  {
    apply approaches_at_add_right,
    apply hf,
  },
  simp only [add_right_neg] at this,
  apply this
end

variables {f g : ℝ → ℝ}

lemma approaches_at_rw (b : ℝ) (a : ℝ)
    (h : approaches_at f b a) (rewrite_rule : ∀ x ≠ a, g x = f x) :
  approaches_at g b a :=
begin
  dsimp [approaches_at],
  intros ε hε,
  specialize h ε hε,
  rcases h with ⟨δ, ⟨hδ, h⟩⟩,
  use [δ, hδ],
  intros x hx,
  specialize h x hx,
  have : x ≠ a, {
    cases hx with hx,
    rw lt_abs at hx,
    cases hx,
    repeat { linarith },
  },
  specialize rewrite_rule x this,
  rw rewrite_rule,
  exact h
end

theorem approaches_at_prod (b₁ : ℝ) (b₂ : ℝ) (a : ℝ)
    (hf : approaches_at f b₁ a) (hg : approaches_at g b₂ a) :
  approaches_at (f*g) (b₁*b₂) a :=
begin
  have h₁ := approaches_at_zero f b₁ a hf,
  have h₂ := approaches_at_zero g b₂ a hg,
  suffices : approaches_at (λ x, (f x - b₁)*(g x - b₂)) 0 a,
  {
    have : ∀ x ≠ a, (f x)*(g x) = (f x - b₁)*(g x - b₂) + b₂*(f x) + b₁*(g x) - b₁*b₂,
    {
      intros, 
      ring,
    },
    apply approaches_at_rw _ _ _ this,
    sorry,
  },
  intros ε hε,
  have : (real.sqrt ε) > 0,
  {
    simp only [gt_iff_lt, real.sqrt_pos],
    apply hε,
  },
  rcases (hf (real.sqrt ε) this) with ⟨δ₁, ⟨hδ₁, hf⟩⟩,
  rcases (hg (real.sqrt ε) this) with ⟨δ₂, ⟨hδ₂, hg⟩⟩,
  clear this,
  use min δ₁ δ₂,
  split,
  {
    simp only [gt_iff_lt, lt_min_iff],
    split,
    repeat { assumption },
  },
  rintros x ⟨hx₀, hxmin⟩,
  simp only [lt_min_iff] at hxmin,
  cases hxmin with hx₁ hx₂,
  specialize hf x ⟨hx₀, hx₁⟩,
  specialize hg x ⟨hx₀, hx₂⟩,
  simp,
  rw abs_mul,
  have : (real.sqrt ε) * (real.sqrt ε) = ε,
  {
    rw [←real.sqrt_mul, real.sqrt_mul_self],
    repeat {
      apply le_of_lt,
      apply hε,
    }
  },
  rw ←this,
  clear this,
  apply mul_lt_mul'',
  repeat { apply abs_nonneg <|> assumption }
end

theorem approaches_at_div (n : ℝ) (d : ℝ) (a : ℝ)
    (hf : approaches_at f n a) (hg : approaches_at g d a) (hd : d ≠ 0) :
  approaches_at (f/g) (n/d) a := sorry

variables {f' g' : ℝ → ℝ} 
  (hf : ∀ (a : ℝ), derivative_at f (f' a) a)    
  (hg : ∀ (a : ℝ), derivative_at g (g' a) a)
  (hf' : continuous f')
  (hg' : continuous g')
include hf hg hf' hg'

theorem lhopitals (b : ℝ) (a : ℝ)
    (hf0 : f a = 0) (hg0 : g a = 0) (hg0' : g' a ≠ 0) :
  approaches_at (f/g) ((f'/g') a) a :=
begin
  have : ∀ x ≠ a, (f x)/(g x) = ((f x - f a)/(x - a))/((g x - g a)/(x - a)),
  {
    intros x hx,
    simp [hf0, hg0],
    apply eq_comm.mpr,
    exact div_div_div_cancel_right (f x) (sub_ne_zero.mpr hx)
  },
  clear hf0 hg0,
  apply approaches_at_rw _ _ _ this,
  apply approaches_at_div,
  apply hf,
  apply hg,
  exact hg0',
end

end lhopitals
