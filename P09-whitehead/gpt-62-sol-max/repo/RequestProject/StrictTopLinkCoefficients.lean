module

public import RequestProject.CellularChainMapZero
public import RequestProject.OrderComplexExt
public import RequestProject.StrictTopLinkChains

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem strictOrderCxMap_onE_injective {Q : Type u} [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f) :
    Function.Injective (strictOrderCxMap f hf).onE :=
  @Hom.injective_chainCx_onE P (· < ·) ⟨fun _ _ _ => lt_trans⟩ (strictOrderCx Q)
    (strictOrderCxMap f hf) hi

/-- An actual injective strict cellular map preserves its edge coefficients. -/
theorem strictOrderCxMap_chain1_apply {Q : Type u} [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f)
    (c : StrictOrdEdge P →₀ ℤ) (e : StrictOrdEdge P) :
    chain1 (strictOrderCxMap f hf) c ((strictOrderCxMap f hf).onE e) = c e := Finsupp.mapDomain_apply_of_injective (strictOrderCxMap_onE_injective f hf hi) c e

/-- An actual order isomorphism induces an equivalence of actual strict edges. -/
def strictOrderEdgeEquiv {Q : Type u} [PartialOrder Q] (e : P ≃o Q) :
    StrictOrdEdge P ≃ StrictOrdEdge Q where
  toFun := (strictOrderCxMap e e.strictMono).onE
  invFun := (strictOrderCxMap e.symm e.symm.strictMono).onE
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [strictOrderCxMap]
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [strictOrderCxMap]

end FiniteChains.Comb
