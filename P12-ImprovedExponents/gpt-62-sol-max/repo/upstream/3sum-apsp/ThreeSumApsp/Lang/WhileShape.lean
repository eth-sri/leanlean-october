module

public import ThreeSumApsp.Lang.Symbolic

public section

namespace Light

variable {lim : Limits} {P : Program} {d T : ℕ} {σ : State} {c : Cond} {body : Stmt}
  {Q : State → Prop}

/-- The same shaped invariant for loops whose time bound varies by round. -/
theorem Ends.whileShapeCosts {β : Type} (S : ℕ → β → (ℕ → ℤ) → State)
    (I : ℕ → β → (ℕ → ℤ) → Prop) (n : ℕ) (b : ℕ → ℕ) (z₀ : β) (μ : ℕ → ℤ)
    (start : I 0 z₀ μ)
    (round : ∀ i z ν, i < n → I i z ν → Ends lim P d body (S i z ν) (b i)
      (fun σ' => ∃ z' ν', σ' = S (i + 1) z' ν' ∧ I (i + 1) z' ν'))
    (done : ∀ z ν, I n z ν → Q (S n z ν))
    (first : σ = S 0 z₀ μ := by rfl)
    (step : ∀ i z ν, i < n → I i z ν → c.Safe lim (S i z ν) ∧ c.Holds (S i z ν) := by
      intros; light_side)
    (stop : ∀ z ν, I n z ν → c.Safe lim (S n z ν) ∧ ¬c.Holds (S n z ν) := by
      intros; light_side)
    (hT : (∑ i ∈ Finset.range n, (c.cost + 1 + b i)) + (c.cost + 1) ≤ T := by light_time) :
    Ends lim P d (.while c body) σ T Q := by
  refine (Ends.while (fun i τ => ∃ z ν, τ = S i z ν ∧ I i z ν) n b
    ⟨z₀, μ, first, start⟩ ?_ ?_).mono hT fun _ h => h
  · rintro i _ hi ⟨z, ν, rfl, h⟩
    exact ⟨(step i z ν hi h).1, (step i z ν hi h).2, round i z ν hi h⟩
  · rintro _ ⟨z, ν, rfl, h⟩
    exact ⟨(stop z ν h).1, (stop z ν h).2, done z ν h⟩

/-- Counted `while` loops with a fixed shape for the locals at the head of each round. -/
theorem Ends.whileShape {β : Type} (S : ℕ → β → (ℕ → ℤ) → State)
    (I : ℕ → β → (ℕ → ℤ) → Prop) (n b : ℕ) (z₀ : β) (μ : ℕ → ℤ)
    (start : I 0 z₀ μ)
    (round : ∀ i z ν, i < n → I i z ν → Ends lim P d body (S i z ν) b
      (fun σ' => ∃ z' ν', σ' = S (i + 1) z' ν' ∧ I (i + 1) z' ν'))
    (done : ∀ z ν, I n z ν → Q (S n z ν))
    (first : σ = S 0 z₀ μ := by rfl)
    (step : ∀ i z ν, i < n → I i z ν → c.Safe lim (S i z ν) ∧ c.Holds (S i z ν) := by
      intros; light_side)
    (stop : ∀ z ν, I n z ν → c.Safe lim (S n z ν) ∧ ¬c.Holds (S n z ν) := by
      intros; light_side)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T := by light_time) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileShapeCosts S I n (fun _ => b) z₀ μ start round done first step stop (by simpa using hT)

end Light
