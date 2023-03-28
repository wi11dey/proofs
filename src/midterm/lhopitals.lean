import assignment5.assignment5

def is_derivative (f : ℝ → ℝ) (f' : ℝ → ℝ) := true

variables (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ)

variables (hf': continuous f') (hg': continuous g')
include hf' hg'

theorem lhopitals (b : ℝ) (a : ℝ) (h: approaches_at (f/g) b a) : approaches_at (f'/g') b a := 
begin
  suffices hvalue : (f' a)/(g' a) = b,
  {
    dsimp [continuous] at hf' hg',
    sorry
  },
  sorry
end
