module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Perm

/-! Finite data for §2 of Weighted dilation graphs. No placeholder proofs. -/

@[expose] public section

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

/-- §1 logarithmic scales. -/
def L (x : ℝ) : ℝ := Real.log x



namespace PrimeGroups


end PrimeGroups


namespace Pattern

end Pattern


namespace Model

-- The maximum does not require a nonempty label space when evaluated via `sSup`.
end Model

namespace Model

end Model

namespace PrimeGroups

end PrimeGroups

namespace PrimeGroups

end PrimeGroups

/-- Birth collections are disjoint nonsingleton blocks of potential addresses. -/
def BirthCollection {a : ℕ} (π : Finset (Finset (Fin a))) : Prop :=
  (∀ B ∈ π, 2 ≤ B.card) ∧ (π : Set (Finset (Fin a))).Pairwise Disjoint

/-- Equality rank adds |B|-1 separately for each block. -/
def birthRank {a : ℕ} (π : Finset (Finset (Fin a))) : ℕ := ∑ B ∈ π, (B.card - 1)

def birthMobius {a : ℕ} (π : Finset (Finset (Fin a))) : ℤ :=
  ∏ B ∈ π, (-1 : ℤ) ^ (B.card - 1) * (Nat.factorial (B.card - 1) : ℤ)

def birthEvent {a : ℕ} (performed : Finset (Fin a)) (value : Fin a → ℕ)
    (π : Finset (Finset (Fin a))) : Prop :=
  ∀ B ∈ π, B ⊆ performed ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j

end Erdos821.S2
