import RequestProject.RelatorCircleFundamentalChain
import RequestProject.StrictTopConeInjectivity
import RequestProject.PresCoverConeCircleProjection
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def relatorCirclePresInclusion (x : RelatorCircle w j) := iCirc w x.val

theorem relatorCirclePresInclusion_strictMono : StrictMono (relatorCirclePresInclusion w j) :=
  by tauto

theorem relatorCirclePresInclusion_lt_apex x :
    relatorCirclePresInclusion w j x < apexOf w j := (relatorCircleToBelow w j x).property
