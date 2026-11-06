module

public import RequestProject.Oriented
public import RequestProject.RelatorCircleFundamentalChain
public import RequestProject.StrictTopConeInjectivity
public import RequestProject.PresCoverConeCircleProjection

@[expose] public section

backwardOptions




namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → FiniteChains.Comb.Oriented α) (j : J)

def relatorCirclePresInclusion (x : RelatorCircle w j) : PresPos w := iCirc w x.val

theorem relatorCirclePresInclusion_strictMono : StrictMono (relatorCirclePresInclusion w j) :=
  fun _ _ h => iCirc_strictMono w h

theorem relatorCirclePresInclusion_lt_apex (x : RelatorCircle w j) :
    relatorCirclePresInclusion w j x < apexOf w j := (relatorCircleToBelow w j x).property

end FiniteChains.PresModel
