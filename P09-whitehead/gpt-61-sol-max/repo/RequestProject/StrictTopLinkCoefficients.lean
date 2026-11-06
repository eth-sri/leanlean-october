import Mathlib.Tactic

import RequestProject.CellularChainMapZero
import RequestProject.StrictTopLinkChains

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P]

/-- The actual triangle over an actual edge in the strict lower interval. -/
def strictConeTriangle (v : P) (e : StrictOrdEdge (StrictBelow v)) : StrictOrdTri P :=
  ⟨(e.1.1.val, e.1.2.val, v), e.2, e.1.2.property⟩

/-- Extracting a link preserves each genuine cone-triangle coefficient. -/
theorem strictTopLinkChain_apply (v : P) (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictBelow v)) :
    strictTopLinkChain v c e = c (strictConeTriangle v e) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    rcases t with ⟨⟨a, b, z⟩, hab, hbz⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · simp_all [strictTopLinkChain, strictTopLinkTriangle, strictConeTriangle, Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictBelow]
    · simp [strictTopLinkChain, strictTopLinkTriangle, ht, strictConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictBelow]

variable {Q : Type u}
theorem strictOrderCxMap_onE_injective  [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f) :
    Function.Injective (strictOrderCxMap f hf).onE := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext
  · apply hi
    exact congrArg (fun t : StrictOrdEdge Q => t.1.1) h
  · apply hi
    exact congrArg (fun t : StrictOrdEdge Q => t.1.2) h

/-- An actual injective strict cellular map preserves its edge coefficients. -/
abbrev strictOrderCxMap_chain1_apply  [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f)
    (c : StrictOrdEdge P →₀ ℤ) (e : StrictOrdEdge P)  :=
  Finsupp.mapDomain_apply_of_injective (FiniteChains.Comb.strictOrderCxMap_onE_injective f hf hi) c e

/-- An actual order isomorphism induces an equivalence of actual strict edges. -/
def strictOrderEdgeEquiv  [PartialOrder Q] (e : P ≃o Q) :
    StrictOrdEdge P ≃ StrictOrdEdge Q where
  toFun := (strictOrderCxMap e e.strictMono).onE
  invFun := (strictOrderCxMap e.symm e.symm.strictMono).onE
  left_inv x := by
    simp_all [strictOrderCxMap]
  right_inv x := by
    simp_all [strictOrderCxMap]

end FiniteChains.Comb
