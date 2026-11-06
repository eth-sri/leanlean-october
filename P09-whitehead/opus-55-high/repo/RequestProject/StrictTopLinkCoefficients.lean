import RequestProject.CellularChainMapZero
import RequestProject.StrictTopLinkChains
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- The actual triangle over an actual edge in the strict lower interval. -/
def strictConeTriangle (v : P) (e : StrictOrdEdge (StrictBelow v)) : StrictOrdTri P :=
  ⟨(e.1.1.val, e.1.2.val, v), e.2, e.1.2.property⟩

/-- Extracting a link preserves each genuine cone-triangle coefficient. -/
theorem strictTopLinkChain_apply v (c : StrictOrdTri P →₀ ℤ)
    e :
    strictTopLinkChain v c e = c (strictConeTriangle v e) := by
  classical
  lin_ind c t n =>
    rcases t with ⟨⟨a, b, z⟩, hab, hbz⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · subst z
      simp [strictTopLinkChain, strictTopLinkTriangle, strictConeTriangle,
        Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictBelow,
        Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictTopLinkChain, strictTopLinkTriangle, ht, strictConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictBelow]

theorem strictOrderCxMap_onE_injective {Q} [PartialOrder Q]
    (f : P → Q) hf (hi : Function.Injective f) :
    Function.Injective (strictOrderCxMap f hf).onE := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext
  · apply hi
    exact congrArg (·.1.1) h
  · apply hi
    exact congrArg (·.1.2) h

/-- An actual injective strict cellular map preserves its edge coefficients. -/
theorem strictOrderCxMap_chain1_apply {Q} [PartialOrder Q]
    (f : P → Q) hf (hi : Function.Injective f)
    (c : StrictOrdEdge P →₀ ℤ) (e : StrictOrdEdge P) :
    chain1 (strictOrderCxMap f hf) c ((strictOrderCxMap f hf).onE e) = c e := Finsupp.mapDomain_apply_of_injective (strictOrderCxMap_onE_injective f hf hi) c e

/-- An actual order isomorphism induces an equivalence of actual strict edges. -/
def strictOrderEdgeEquiv {Q : Type u} [PartialOrder Q] (e : P ≃o Q) :
    StrictOrdEdge P ≃ StrictOrdEdge Q where
  toFun := (strictOrderCxMap e e.strictMono).onE
  invFun := (strictOrderCxMap e.symm e.symm.strictMono).onE
  left_inv x := by
    simp [strictOrderCxMap]
  right_inv x := by
    simp [strictOrderCxMap]
