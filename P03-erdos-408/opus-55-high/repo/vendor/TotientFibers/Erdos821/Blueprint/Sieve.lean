module

public import Erdos821.Blueprint.Classical
public import Mathlib.Data.Nat.Squarefree

/-! P2: the block sieve, including its coefficient and level certificates. -/

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint

structure SieveData (α : Type) where
  objects : Finset α
  weight : α → ℝ
  primes : Finset ℕ
  bad : ℕ → α → Prop
  X : ℝ
  density : ℕ → ℝ
  nonneg : ∀ a ∈ objects, 0 ≤ weight a
  prime : ∀ p ∈ primes, p.Prime
  X_nonneg : 0 ≤ X

namespace SieveData
variable {α : Type} (S : SieveData α)
end SieveData




end Erdos821.Blueprint
