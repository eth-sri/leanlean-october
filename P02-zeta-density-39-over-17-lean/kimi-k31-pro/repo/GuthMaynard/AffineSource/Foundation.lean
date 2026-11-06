module
public import MathCollab.Density.DivisorGrowth

@[expose] public section
namespace RiemannZeta.GuthMaynard

noncomputable def gmIntDecayProfile (q : ℕ) (m : ℤ) : ℝ :=
  if m = 0 then 0 else 1 / |(m : ℝ)| ^ q

def DivisorCountBoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

theorem divisorCountBound_native : DivisorCountBoundProp := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := MathCollab.Density.divisor_card_subpower hε
  exact ⟨C,by linarith,h⟩

end RiemannZeta.GuthMaynard
