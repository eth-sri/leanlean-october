import Mathlib.Tactic

import RequestProject.RelatorCircleFundamentalChain
import RequestProject.StrictTopConeInjectivity
import RequestProject.PresCoverConeCircleProjection

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel

variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def relatorCirclePresInclusion (x : RelatorCircle w j)  := iCirc w x.val

theorem relatorCirclePresInclusion_strictMono : StrictMono (relatorCirclePresInclusion w j) :=
  fun _ _ h => iCirc_strictMono w h

abbrev relatorCirclePresInclusion_lt_apex (x : RelatorCircle w j)  :=
  (FiniteChains.PresModel.relatorCircleToBelow w j x).property

end FiniteChains.PresModel
