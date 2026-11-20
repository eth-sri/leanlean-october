module

public import RequestProject.UnivCoverIncl
public import RequestProject.OrderComplexGluing

@[expose] public section

/-! Explicit finite cellular cone fillings, rather than unspecified null-homotopy witnesses. -/

noncomputable section

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)

def coneRadial (x : P) : (orderCx Q).E := ⟨(c, f x), hc x⟩
def coneEdgeTriangle (e : (orderCx P).E) : (orderCx Q).F :=
  ⟨(c, f _, f _), hc _, hf e.2⟩
def coneEdgeChain :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (coneEdgeTriangle f hf c hc e) (1 : ℤ))

end FiniteChains.Comb
