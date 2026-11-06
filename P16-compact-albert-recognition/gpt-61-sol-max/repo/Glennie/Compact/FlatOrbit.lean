module

public import Glennie.Compact.Affine20.Relabel

@[expose] public section

namespace Glennie.Compact.FlatOrbit

open Glennie Glennie.Compact.Affine20

noncomputable section
/-- The identity acts trivially. -/
theorem mapAtoms_refl (T : Triple) :
    mapAtoms Glennie.CompactAutomorphism.refl T = T := by
  funext a i
  show Glennie.CompactAutomorphism.refl.equiv (T a i) = T a i
  rfl

/-- The action is associative. -/
theorem mapAtoms_comp (g h : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g (mapAtoms h T) = mapAtoms (g.comp h) T := rfl

/-- The action is invertible. -/
theorem mapAtoms_symm_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g.symm (mapAtoms g T) = T := by
  funext a i
  show g.equiv.symm (g.equiv (T a i)) = T a i
  exact g.equiv.symm_apply_apply (T a i)

/-- The compact automorphism orbit of an ordered triple. The group is
`Glennie.CompactAutomorphism` (`Obligations.lean`): a real-linear equivalence of
`Albert` preserving the native Jordan product and the trace. No compactness of the
group as a topological group, and no identification with F4, is used or claimed. -/
def autOrbit (S : Triple) : Set Triple :=
  {T : Triple | ∃ g : Glennie.CompactAutomorphism, mapAtoms g S = T}

/-- Frames are preserved slotwise, by `map_frame` (`Automorphism.lean`). -/
theorem frame_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple)
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) (a : Fin 3) :
    Glennie.Frame (mapAtoms g T a) :=
  g.map_frame (T a) (hT a)

end
end Glennie.Compact.FlatOrbit
