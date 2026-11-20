module

public import RequestProject.PresCylinderCoverCycles
public import RequestProject.ConeAdjBaseCover
public import RequestProject.StrictSubposetChains

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)
include hf

/-- The actual preimage of the cylinder has no strict two-cycles. -/
theorem presCover_cylinder_preimage_cycle_zero
    (c : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet} →₀ ℤ)
    (hc : Comb.bdry2
      (strictOrderCx {p : P // f p ∈ coneAdjBaseSet}) c = 0) : c = 0 :=
  cylinderCover_two_cycle_zero w (coneAdjCoverBaseEnd_isPosetCover f hf) c hc

end FiniteChains.PresModel
