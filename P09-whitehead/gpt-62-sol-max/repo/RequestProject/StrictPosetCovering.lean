module

public import RequestProject.OrderPosetCovering
public import RequestProject.PosetCoverUpTransform
public import RequestProject.StrictOrderComplex

@[expose] public section

/-! A poset covering restricts to the genuine nondegenerate cellular
two-skeleton. This is the cover used with strict cellular acyclicity.
Unverified source. -/

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

def strictMap : Hom (strictOrderCx P) (strictOrderCx Q) := strictOrderCxMap f hf.strictMono

theorem strictMap_isCovering : IsCovering hf.strictMap :=
  hf.isCovering_chainCxMap (r := (· < ·)) (s := (· < ·))
    (hr := ⟨fun _ _ _ => lt_trans⟩) (hs := ⟨fun _ _ _ => lt_trans⟩)
    (fun h => h.le) (fun h => h.le) (fun h => hf.strictMono h)
    (fun h h' => lt_of_le_of_ne h (fun e => h'.ne (congrArg f e)))

end FiniteChains.Comb.IsPosetCover
