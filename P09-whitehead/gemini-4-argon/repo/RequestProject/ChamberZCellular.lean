module

public import RequestProject.NerveDegree
public import RequestProject.ChamberZChain
public import RequestProject.OrderNerveDecoding

@[expose] public section

/-! Cellular two-cycle generation for the actual modified-chamber poset. -/

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

instance zposPartialOrder : PartialOrder (Zpos A X M att) where
  toPreorder := zposPreorder
  le_antisymm s t hst hts := by
    cases s with
    | inl p =>
      cases t with
      | inl q => exact congrArg Sum.inl (Subtype.ext (le_antisymm hst hts))
      | inr y => exact hst.elim
    | inr wx =>
      cases t with
      | inl p => exact hts.elim
      | inr vy => exact congrArg Sum.inr (Prod.ext hst.1 (le_antisymm hst.2 hts.2))
