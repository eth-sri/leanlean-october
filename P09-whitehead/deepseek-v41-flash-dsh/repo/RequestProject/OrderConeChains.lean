module

public import RequestProject.UnivCoverIncl
public import RequestProject.OrderComplexGluing

@[expose] public section

/-! Explicit finite cellular cone fillings, rather than unspecified null-homotopy witnesses. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)

noncomputable def coneRadial (x : P) : (orderCx Q).E := ⟨(c, f x), hc x⟩
noncomputable def coneEdgeTriangle (e : (orderCx P).E) : (orderCx Q).F :=
  ⟨(c, f e.1.1, f e.1.2), hc _, hf e.2⟩
noncomputable def coneEdgeChain : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] ((orderCx Q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (coneEdgeTriangle f hf c hc e) (1 : ℤ))

end FiniteChains.Comb
