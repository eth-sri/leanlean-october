module

public import RequestProject.StrictOrderComplex
public import RequestProject.ChamberQuotientCover

@[expose] public section

/-! The chamber group injection in the genuine, nondegenerate simplicial model. -/

namespace FiniteChains.Davis
open RACG Comb
universe u
variable {V X : Type u} [DecidableEq V] {A : CommRel V}
  [PartialOrder X] {att : NeSpx A →o X}

instance qposPartialOrder : PartialOrder (Qpos A X att) where
  toPreorder := qposPreorder
  le_antisymm s t hst hts := by
    cases s with
    | inl c =>
      cases t with
      | inl d => exact congrArg Sum.inl (Subtype.ext (le_antisymm hst hts))
      | inr y => exact hst.elim
    | inr x =>
      cases t with
      | inl d => exact hts.elim
      | inr y => exact congrArg Sum.inr (le_antisymm hst hts)
