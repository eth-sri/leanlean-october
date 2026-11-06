module

public import RequestProject.RelatorCircleFundamentalChain
public import RequestProject.StrictTopConeInjectivity
public import RequestProject.PresCoverConeCircleProjection

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def relatorCirclePresInclusion (x : RelatorCircle w j) : PresPos w := iCirc w x.val

theorem relatorCirclePresInclusion_strictMono : StrictMono (relatorCirclePresInclusion w j) :=
  fun _ _ h => iCirc_strictMono w h

theorem relatorCirclePresInclusion_lt_apex (x : RelatorCircle w j) :
    relatorCirclePresInclusion w j x < apexOf w j := (relatorCircleToBelow w j x).property

end FiniteChains.PresModel
