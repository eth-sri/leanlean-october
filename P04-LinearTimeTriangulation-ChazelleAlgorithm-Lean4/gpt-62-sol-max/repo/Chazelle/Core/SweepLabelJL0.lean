module

public import Chazelle.Core.SweepLabelJL
public import Chazelle.Core.SweepLabelGap

/-!
# The sweep (WP-D): the left correspondence without `TopStrict` (F2)

`corr_left0`: the correspondence of `corr_left` without its gap field `box` (`Corr0`), which is
the only place where `corr_left` uses `TopStrict J.left`.  The side-0 sweep lemmas use only
`sidePt_eq`, `attach_iff`, `faces_iff` and the offsets, which `Corr0` provides.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft sidePrev sideNext)
open Chazelle.Visibility (rayPt)
open WalkEmbed

namespace Sweep

variable (J : Merge.Junction)

theorem corr_left0 (hP : J.P.Simple) {S₁ : Set (Set Point)}
    (hS₁ : S₁ ⊆ Merge.augChords J.left) (hS₁f : S₁.Finite) :
    Corr0 J.wholeModel J.leftModel (F₁plus J S₁) S₁
      (6 + tpos J.whole (J.m₁ + 2 * J.m₂)) (6 + tpos J.left J.m₁) (lL1 J) (lL2 J) (lδ J) := by
  apply corr0_of_tour hP hP (F₁plus_subset J hS₁) (F₁plus_finite J hS₁f) hS₁ hS₁f
    (by have := J.one_le_m₂; change 2 * J.m₁ < 2 * (J.m₁ + J.m₂); omega)
    (FuseMath.radius_of_P J rfl).symm (fun _ h => tourV_left J h)
    (fun h => (left_box_eq J h).symm)
  · intro p t hp ht ht1 hv
    rw [tourV_left_zero, show J.shared = J.left.vertex J.left.m from rfl] at hv
    exact off_vertexEnd J.left hP hp ht ht1 hv
  · rw [tourV_left_zero]
    exact trans_left J hP hS₁

end Sweep

end

end Chazelle.Core
