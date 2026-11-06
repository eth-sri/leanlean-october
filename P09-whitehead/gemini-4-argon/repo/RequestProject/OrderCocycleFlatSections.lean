module

public import RequestProject.OrderCocyclePotential

@[expose] public section

/-! Flat sections for arbitrary group actions, retaining nonabelian monodromy. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω] (c : OrdCocycle P G)

def IsFlatSection (s : P → Ω) : Prop :=
  ∀ {a b}, a ≤ b → c.val a b • s b = s a
