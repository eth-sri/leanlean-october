module

public import RequestProject.RelatorCircleFundamentalChain
public import RequestProject.StrictTopConeInjectivity
public import RequestProject.PresCoverConeCircleProjection

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def relatorCirclePresInclusion (x : RelatorCircle w j) := iCirc w x.val

theorem relatorCirclePresInclusion_strictMono : StrictMono (relatorCirclePresInclusion w j) :=
  fun _ _ h => iCirc_strictMono w h

theorem relatorCirclePresInclusion_lt_apex (x : RelatorCircle w j) :
    relatorCirclePresInclusion w j x < apexOf w j := (relatorCircleToBelow w j x).property

end FiniteChains.PresModel
