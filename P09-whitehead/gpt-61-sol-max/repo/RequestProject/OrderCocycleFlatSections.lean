import Mathlib.Tactic

import RequestProject.OrderCocyclePotential

/-! Flat sections for arbitrary group actions, retaining nonabelian monodromy. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω] (c : OrdCocycle P G)

def IsFlatSection (s : P → Ω)  :=
  ∀ {a b}, a ≤ b → c.val a b • s b = s a

end FiniteChains.Comb.OrdCocycle
