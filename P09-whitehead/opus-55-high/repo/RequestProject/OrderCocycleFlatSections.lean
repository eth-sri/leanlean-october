import RequestProject.OrderCocyclePotential
import RequestProject.Tac


/-! Flat sections for arbitrary group actions, retaining nonabelian monodromy. -/
bwd

namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω] (c : OrdCocycle P G)

def IsFlatSection (s : P → Ω) :=
  ∀ {a b}, a ≤ b → c.val a b • s b = s a
